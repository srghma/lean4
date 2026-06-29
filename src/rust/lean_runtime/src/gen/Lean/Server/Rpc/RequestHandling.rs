// Lean compiler output
// Module: Lean.Server.Rpc.RequestHandling
// Imports: Lean.Server.Requests
use crate::r#gen::Init::Core::l_Prod_map___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_quoteNameMk, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node4, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
    l_id___boxed,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::Attributes::{
    l_Lean_ensureAttrDeclIsMeta, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_markMeta;
use crate::r#gen::Lean::CoreM::l_Lean_compileDecl;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Data::Lsp::Extra::l_Lean_Lsp_instFromJsonRpcCallParams_fromJson;
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_FileMap_lspPosToUtf8Pos;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_contains___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkCollisionNode___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntries, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_TermElabM_run___redArg, l_Lean_Elab_Term_elabTerm,
    l_Lean_Elab_Term_withoutErrToSorryImp___redArg,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_contains___redArg,
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_evalConstCheck___redArg,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_mkConst};
use crate::r#gen::Lean::ImportingFlag::l_Lean_initializing;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Server::Requests::{
    initialize_Lean_Server_Requests, l_Lean_Server_RequestM_asTask___redArg,
    l_Lean_Server_RequestM_bindWaitFindSnap___redArg, l_Lean_Server_RequestM_mapTaskCheap___redArg,
    l_Lean_Server_instInhabitedRequestError_default, l_Lean_Server_requestHandlers,
    runtime_initialize_Lean_Server_Requests,
};
use crate::r#gen::Lean::Server::ServerTask::l_Lean_Server_ServerTask_mapCheap___redArg;
use crate::r#gen::Lean::Server::Snapshots::{
    l_Lean_Server_Snapshots_Snapshot_endPos, l_Lean_Server_Snapshots_Snapshot_env,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_intercalate;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_dec_lt, lean_uint64_to_usize, lean_usize_land, lean_usize_mul,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq, lean_string_hash, lean_uint64_dec_eq,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_wait;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_Server_instInhabitedRpcProcedure_default___closed__0_value:
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
    m_fun: l_Lean_Server_instInhabitedRpcProcedure_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instInhabitedRpcProcedure_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedRpcProcedure_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instInhabitedRpcProcedure_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedRpcProcedure_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instInhabitedRpcProcedure: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedRpcProcedure_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 101, 114, 118, 101, 114, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [117, 115, 101, 114, 82, 112, 99, 80, 114, 111, 99, 101, 100, 117, 114, 101, 115, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10364845582346621728 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_userRpcProcedures: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [82, 112, 99, 80, 114, 111, 99, 101, 100, 117, 114, 101, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__0_value) as *mut crate::leanh::LeanObject,2223063512036383317 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_Server_handleRpcCall___lam__3___closed__0_value: crate::leanh::LeanStringObject<
    34,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 82,
        80, 67, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 39, 0,
    ],
};
static mut l_Lean_Server_handleRpcCall___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleRpcCall___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleRpcCall___lam__3___closed__1_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [39, 58, 32, 0],
};
static mut l_Lean_Server_handleRpcCall___lam__3___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleRpcCall___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleRpcCall___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
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
            78, 111, 32, 82, 80, 67, 32, 109, 101, 116, 104, 111, 100, 32, 39, 0,
        ],
    };
static mut l_Lean_Server_handleRpcCall___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleRpcCall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_handleRpcCall___closed__1_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [39, 32, 102, 111, 117, 110, 100, 0],
    };
static mut l_Lean_Server_handleRpcCall___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_handleRpcCall___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [67, 97, 110, 110, 111, 116, 32, 112, 97, 114, 115, 101, 32, 114, 101, 113, 117, 101, 115, 116, 32, 112, 97, 114, 97, 109, 115, 58, 32, 0]};
static mut l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0_value: crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32, 76, 83, 80, 32, 114, 101, 113, 117, 101, 115, 116, 32, 104, 97, 110, 100, 108, 101, 114, 32, 102, 111, 114, 32, 39, 0]};
static mut l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [39, 58, 32, 111, 110, 108, 121, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 100, 117, 114, 105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [39, 58, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 0]};
static mut l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [36, 47, 108, 101, 97, 110, 47, 114, 112, 99, 47, 99, 97, 108, 108, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_handleRpcCall___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 112, 97, 114, 97, 109,
        115, 32, 105, 110, 32, 82, 80, 67, 32, 99, 97, 108, 108, 32, 39, 0,
    ],
};
static mut l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1_value:
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
    m_data: [40, 0],
};
static mut l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2_value:
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
    m_data: [41, 39, 10, 0],
};
static mut l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__3_value:
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
        79, 117, 116, 100, 97, 116, 101, 100, 32, 82, 80, 67, 32, 115, 101, 115, 115, 105, 111,
        110, 0,
    ],
};
static mut l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__3_value)
            as *mut crate::leanh::LeanObject,
        9 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_wrapRpcProcedure___redArg___closed__0_value:
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
    m_fun: l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_wrapRpcProcedure___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_wrapRpcProcedure___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32,
        98, 117, 105, 108, 116, 105, 110, 32, 82, 80, 67, 32, 99, 97, 108, 108, 32, 104, 97, 110,
        100, 108, 101, 114, 32, 102, 111, 114, 32, 39, 0,
    ],
};
static mut l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1_value:
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
    m_data: [39, 0],
};
static mut l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2_value:
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
        58, 32, 111, 110, 108, 121, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 100, 117, 114,
        105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3_value:
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
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4_value:
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
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5_value:
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
        58, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101,
        100, 0,
    ],
};
static mut l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__0_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__1_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__2_value:
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
    m_data: [97, 112, 112, 0],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__3_value:
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
        119, 114, 97, 112, 82, 112, 99, 80, 114, 111, 99, 101, 100, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        10678004992931396190 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__6_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__8_value:
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
    m_data: [104, 111, 108, 101, 0],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__9_value:
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
    m_data: [95, 0],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__10_value:
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
    m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__11_value:
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
    m_data: [96, 0],
};
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___lam__1___closed__12_value:
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
static mut l_Lean_Server_registerRpcProcedure___lam__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___lam__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_registerRpcProcedure___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Server_registerRpcProcedure___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_registerRpcProcedure___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___closed__1_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Server_registerRpcProcedure___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___closed__2_value: crate::leanh::LeanCtorObject<10> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                + 16) as u16,
            other: 8,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__1_value)
                as *mut crate::leanh::LeanObject,
            16843009 as *mut crate::leanh::LeanObject,
            65537 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Server_registerRpcProcedure___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 24) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [
            282574488338432 as *mut crate::leanh::LeanObject,
            72621647814721793 as *mut crate::leanh::LeanObject,
            65793 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Server_registerRpcProcedure___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_registerRpcProcedure___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__4: u64 = 0;
static mut l_Lean_Server_registerRpcProcedure___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_registerRpcProcedure___closed__15_value: crate::leanh::LeanCtorObject<7> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
                + 0) as u16,
            other: 7,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Server_registerRpcProcedure___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___closed__16_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [95, 114, 112, 99, 95, 119, 114, 97, 112, 112, 101, 100, 0],
};
static mut l_Lean_Server_registerRpcProcedure___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_registerRpcProcedure___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__16_value)
                as *mut crate::leanh::LeanObject,
            14809249512337240396 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Server_registerRpcProcedure___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_registerRpcProcedure___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_registerRpcProcedure___closed__19_value: crate::leanh::LeanStringObject<
    42,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32,
        82, 80, 67, 32, 99, 97, 108, 108, 32, 104, 97, 110, 100, 108, 101, 114, 32, 102, 111, 114,
        32, 39, 0,
    ],
};
static mut l_Lean_Server_registerRpcProcedure___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_registerRpcProcedure___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_registerRpcProcedure___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_registerRpcProcedure___closed__23_value: crate::leanh::LeanStringObject<
    31,
> = crate::leanh::LeanStringObject {
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
        58, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101,
        100, 32, 40, 98, 117, 105, 108, 116, 105, 110, 41, 0,
    ],
};
static mut l_Lean_Server_registerRpcProcedure___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_registerRpcProcedure___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_registerRpcProcedure___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_registerRpcProcedure___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12337524736695414095 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 112, 99, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12321304609767472988 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [82, 101, 113, 117, 101, 115, 116, 72, 97, 110, 100, 108, 105, 110, 103, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__7_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7747945527765741695 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__7_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__7_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__8_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__7_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1931925011373772594 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__8_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__8_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__9_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__8_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5886820593572843699 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__9_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__9_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__10_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__9_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3532844291300785730 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__10_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__10_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__11_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__11_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__11_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__12_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__10_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__11_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3459608569907588791 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__12_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__12_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__13_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__13_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__13_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__14_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__12_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__13_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17011641794318634994 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__14_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__14_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__15_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__14_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8651383293427974259 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__15_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__15_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__16_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__15_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4022353689453521154 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__16_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__16_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__17_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__16_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13565275497972556981 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__17_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__17_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__18_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__17_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__6_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1021453866249121138 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__18_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__18_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__19_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__18_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1988373275 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,8800774739252253295 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__19_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__19_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__20_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__20_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__20_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__21_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__19_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__20_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7064207869032536932 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__21_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__21_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__22_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__22_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__22_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__23_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__21_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__22_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,858993242565799408 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__23_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__23_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__24_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__23_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3864034271123437217 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__24_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__24_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__25_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [115, 101, 114, 118, 101, 114, 95, 114, 112, 99, 95, 109, 101, 116, 104, 111, 100, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__25_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__25_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__25_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7126996809954302780 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__27_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__27_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__27_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__28_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__28_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__28_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__29_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<209> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 209, m_capacity: 209, m_length: 202, m_data: [77, 97, 114, 107, 115, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 76, 101, 97, 110, 32, 115, 101, 114, 118, 101, 114, 32, 82, 80, 67, 32, 109, 101, 116, 104, 111, 100, 46, 10, 32, 32, 32, 32, 83, 104, 111, 114, 116, 104, 97, 110, 100, 32, 102, 111, 114, 32, 96, 114, 101, 103, 105, 115, 116, 101, 114, 82, 112, 99, 80, 114, 111, 99, 101, 100, 117, 114, 101, 96, 46, 10, 32, 32, 32, 32, 84, 104, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 32, 96, 206, 177, 32, 226, 134, 146, 32, 82, 101, 113, 117, 101, 115, 116, 77, 32, 40, 82, 101, 113, 117, 101, 115, 116, 84, 97, 115, 107, 32, 206, 178, 41, 96, 32, 119, 105, 116, 104, 10, 32, 32, 32, 32, 96, 91, 82, 112, 99, 69, 110, 99, 111, 100, 97, 98, 108, 101, 32, 206, 177, 93, 96, 32, 97, 110, 100, 32, 96, 91, 82, 112, 99, 69, 110, 99, 111, 100, 97, 98, 108, 101, 32, 206, 178, 93, 96, 46, 0]};
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__29_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__29_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__30_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__24_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__26_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__29_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__30_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__30_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__30_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__27_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__28_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Server_instInhabitedRpcProcedure_default___lam__0(
    mut v_x_1810_: u64,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = l_Lean_Server_instInhabitedRequestError_default;
    v___x_1815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1815_, 0, v___x_1814_);
    return v___x_1815_;
}
pub unsafe fn l_Lean_Server_instInhabitedRpcProcedure_default___lam__0___boxed(
    mut v_x_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
    mut v___y_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_55__boxed_1820_: u64 = 0;
    let mut v_res_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_55__boxed_1820_ = crate::leanh::lean_unbox_uint64(v_x_1816_);
    crate::leanh::lean_dec_ref(v_x_1816_);
    v_res_1821_ = l_Lean_Server_instInhabitedRpcProcedure_default___lam__0(
        v_x_55__boxed_1820_,
        v___y_1817_,
        v___y_1818_,
    );
    crate::leanh::lean_dec_ref(v___y_1818_);
    crate::leanh::lean_dec(v___y_1817_);
    return v_res_1821_;
}
pub unsafe fn _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1825_;
}
pub unsafe fn _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
    v___x_1827_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1826_);
    return v___x_1827_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1829_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_);
    v___x_1830_ = lean_st_mk_ref(v___x_1829_);
    v___x_1831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1831_, 0, v___x_1830_);
    return v___x_1831_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2____boxed(
    mut v_a_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1833_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_();
    return v_res_1833_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_1834_: *mut crate::leanh::LeanObject,
    mut v_x_1835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1835_) == 0 {
                    v_k_1836_ = crate::leanh::lean_ctor_get(v_x_1835_, 1);
                    v_v_1837_ = crate::leanh::lean_ctor_get(v_x_1835_, 2);
                    v_l_1838_ = crate::leanh::lean_ctor_get(v_x_1835_, 3);
                    v_r_1839_ = crate::leanh::lean_ctor_get(v_x_1835_, 4);
                    v___x_1840_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_1834_, v_l_1838_);
                    crate::leanh::lean_inc(v_v_1837_);
                    crate::leanh::lean_inc(v_k_1836_);
                    v___x_1841_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1841_, 0, v_k_1836_);
                    crate::leanh::lean_ctor_set(v___x_1841_, 1, v_v_1837_);
                    v___x_1842_ = lean_array_push(v___x_1840_, v___x_1841_);
                    v_init_1834_ = v___x_1842_;
                    v_x_1835_ = v_r_1839_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1834_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_1844_: *mut crate::leanh::LeanObject,
    mut v_x_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_1844_, v_x_1845_);
    crate::leanh::lean_dec(v_x_1845_);
    return v_res_1846_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(
    mut v_env_1847_: *mut crate::leanh::LeanObject,
    mut v_as_1848_: *mut crate::leanh::LeanObject,
    mut v_i_1849_: usize,
    mut v_stop_1850_: usize,
    mut v_b_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: usize = 0;
    let mut v___x_1855_: usize = 0;
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: u8 = 0;
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1857_ = lean_usize_dec_eq(v_i_1849_, v_stop_1850_);
                if v___x_1857_ == 0 {
                    v___x_1858_ = lean_array_uget_borrowed(v_as_1848_, v_i_1849_);
                    v_fst_1859_ = crate::leanh::lean_ctor_get(v___x_1858_, 0);
                    crate::leanh::lean_inc(v_fst_1859_);
                    crate::leanh::lean_inc_ref(v_env_1847_);
                    v___x_1860_ =
                        l_Lean_Environment_contains(v_env_1847_, v_fst_1859_, v___x_1857_);
                    if v___x_1860_ == 0 {
                        v___y_1853_ = v_b_1851_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_1858_);
                        v___x_1861_ = lean_array_push(v_b_1851_, v___x_1858_);
                        v___y_1853_ = v___x_1861_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1847_);
                    return v_b_1851_;
                }
            }
            1 => {
                v___x_1854_ = 1usize;
                v___x_1855_ = lean_usize_add(v_i_1849_, v___x_1854_);
                v_i_1849_ = v___x_1855_;
                v_b_1851_ = v___y_1853_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_1862_: *mut crate::leanh::LeanObject,
    mut v_as_1863_: *mut crate::leanh::LeanObject,
    mut v_i_1864_: *mut crate::leanh::LeanObject,
    mut v_stop_1865_: *mut crate::leanh::LeanObject,
    mut v_b_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1867_: usize = 0;
    let mut v_stop_boxed_1868_: usize = 0;
    let mut v_res_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1867_ = crate::leanh::lean_unbox_usize(v_i_1864_);
    crate::leanh::lean_dec(v_i_1864_);
    v_stop_boxed_1868_ = crate::leanh::lean_unbox_usize(v_stop_1865_);
    crate::leanh::lean_dec(v_stop_1865_);
    v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_1862_, v_as_1863_, v_i_boxed_1867_, v_stop_boxed_1868_, v_b_1866_);
    crate::leanh::lean_dec_ref(v_as_1863_);
    return v_res_1869_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(
    mut v_env_1876_: *mut crate::leanh::LeanObject,
    mut v_s_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    v___x_1878_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1879_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_;
    v___x_1880_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v___x_1879_, v_s_1877_);
    v___x_1881_ = lean_array_get_size(v___x_1880_);
    v___x_1882_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_;
    v___x_1883_ = lean_nat_dec_lt(v___x_1878_, v___x_1881_);
    if v___x_1883_ == 0 {
        let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1880_);
        crate::leanh::lean_dec_ref(v_env_1876_);
        v___x_1884_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_;
        return v___x_1884_;
    } else {
        let mut v___x_1885_: u8 = 0;
        v___x_1885_ = lean_nat_dec_le(v___x_1881_, v___x_1881_);
        if v___x_1885_ == 0 {
            if v___x_1883_ == 0 {
                let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_1880_);
                crate::leanh::lean_dec_ref(v_env_1876_);
                v___x_1886_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_;
                return v___x_1886_;
            } else {
                let mut v___x_1887_: usize = 0;
                let mut v___x_1888_: usize = 0;
                let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1887_ = 0usize;
                v___x_1888_ = lean_usize_of_nat(v___x_1881_);
                v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_1876_, v___x_1880_, v___x_1887_, v___x_1888_, v___x_1882_);
                crate::leanh::lean_dec_ref(v___x_1880_);
                crate::leanh::lean_inc_ref_n(v___x_1889_, 2);
                v___x_1890_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1890_, 0, v___x_1889_);
                crate::leanh::lean_ctor_set(v___x_1890_, 1, v___x_1889_);
                crate::leanh::lean_ctor_set(v___x_1890_, 2, v___x_1889_);
                return v___x_1890_;
            }
        } else {
            let mut v___x_1891_: usize = 0;
            let mut v___x_1892_: usize = 0;
            let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1891_ = 0usize;
            v___x_1892_ = lean_usize_of_nat(v___x_1881_);
            v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__1(v_env_1876_, v___x_1880_, v___x_1891_, v___x_1892_, v___x_1882_);
            crate::leanh::lean_dec_ref(v___x_1880_);
            crate::leanh::lean_inc_ref_n(v___x_1893_, 2);
            v___x_1894_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1894_, 0, v___x_1893_);
            crate::leanh::lean_ctor_set(v___x_1894_, 1, v___x_1893_);
            crate::leanh::lean_ctor_set(v___x_1894_, 2, v___x_1893_);
            return v___x_1894_;
        }
    }
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(
    mut v_env_1895_: *mut crate::leanh::LeanObject,
    mut v_s_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_(v_env_1895_, v_s_1896_);
    crate::leanh::lean_dec(v_s_1896_);
    return v_res_1897_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1909_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_;
    v___x_1910_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__4_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_;
    v___x_1911_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__5_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_;
    v___x_1912_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_1910_, v___x_1911_, v___f_1909_);
    return v___x_1912_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2____boxed(
    mut v_a_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1914_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_();
    return v_res_1914_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0(
    mut v_init_1915_: *mut crate::leanh::LeanObject,
    mut v_t_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0_spec__0(v_init_1915_, v_t_1916_);
    return v___x_1917_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_1918_: *mut crate::leanh::LeanObject,
    mut v_t_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2__spec__0(v_init_1918_, v_t_1919_);
    crate::leanh::lean_dec(v_t_1919_);
    return v_res_1920_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(
    mut v_env_1926_: *mut crate::leanh::LeanObject,
    mut v_opts_1927_: *mut crate::leanh::LeanObject,
    mut v_procName_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1929_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1;
    v___x_1930_ = l_Lean_Environment_evalConstCheck___redArg(
        v_env_1926_,
        v_opts_1927_,
        v___x_1929_,
        v_procName_1928_,
    );
    return v___x_1930_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___boxed(
    mut v_env_1931_: *mut crate::leanh::LeanObject,
    mut v_opts_1932_: *mut crate::leanh::LeanObject,
    mut v_procName_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(
        v_env_1931_,
        v_opts_1932_,
        v_procName_1933_,
    );
    crate::leanh::lean_dec_ref(v_opts_1932_);
    return v_res_1934_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1935_: *mut crate::leanh::LeanObject,
    mut v_i_1936_: *mut crate::leanh::LeanObject,
    mut v_k_1937_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: u8 = 0;
    let mut v_k_x27_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1938_ = lean_array_get_size(v_keys_1935_);
                v___x_1939_ = lean_nat_dec_lt(v_i_1936_, v___x_1938_);
                if v___x_1939_ == 0 {
                    crate::leanh::lean_dec(v_i_1936_);
                    return v___x_1939_;
                } else {
                    v_k_x27_1940_ = lean_array_fget_borrowed(v_keys_1935_, v_i_1936_);
                    v___x_1941_ = lean_name_eq(v_k_1937_, v_k_x27_1940_);
                    if v___x_1941_ == 0 {
                        v___x_1942_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1943_ = lean_nat_add(v_i_1936_, v___x_1942_);
                        crate::leanh::lean_dec(v_i_1936_);
                        v_i_1936_ = v___x_1943_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_1936_);
                        return v___x_1941_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1945_: *mut crate::leanh::LeanObject,
    mut v_i_1946_: *mut crate::leanh::LeanObject,
    mut v_k_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1948_: u8 = 0;
    let mut v_r_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1948_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_keys_1945_, v_i_1946_, v_k_1947_);
    crate::leanh::lean_dec(v_k_1947_);
    crate::leanh::lean_dec_ref(v_keys_1945_);
    v_r_1949_ = crate::leanh::lean_box((v_res_1948_) as usize);
    return v_r_1949_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: usize = 0;
    let mut v___x_1952_: usize = 0;
    v___x_1950_ = 5usize;
    v___x_1951_ = 1usize;
    v___x_1952_ = lean_usize_shift_left(v___x_1951_, v___x_1950_);
    return v___x_1952_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1953_: usize = 0;
    let mut v___x_1954_: usize = 0;
    let mut v___x_1955_: usize = 0;
    v___x_1953_ = 1usize;
    v___x_1954_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__0);
    v___x_1955_ = lean_usize_sub(v___x_1954_, v___x_1953_);
    return v___x_1955_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(
    mut v_x_1956_: *mut crate::leanh::LeanObject,
    mut v_x_1957_: usize,
    mut v_x_1958_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: usize = 0;
    let mut v___x_1962_: usize = 0;
    let mut v___x_1963_: usize = 0;
    let mut v_j_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: u8 = 0;
    let mut v_node_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: usize = 0;
    let mut v___x_1971_: u8 = 0;
    let mut v_ks_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1956_) == 0 {
                    v_es_1959_ = crate::leanh::lean_ctor_get(v_x_1956_, 0);
                    v___x_1960_ = crate::leanh::lean_box(2);
                    v___x_1961_ = 5usize;
                    v___x_1962_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
                    v___x_1963_ = lean_usize_land(v_x_1957_, v___x_1962_);
                    v_j_1964_ = lean_usize_to_nat(v___x_1963_);
                    v___x_1965_ = lean_array_get_borrowed(v___x_1960_, v_es_1959_, v_j_1964_);
                    crate::leanh::lean_dec(v_j_1964_);
                    match crate::leanh::lean_obj_tag(v___x_1965_) {
                        0 => {
                            v_key_1966_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                            v___x_1967_ = lean_name_eq(v_x_1958_, v_key_1966_);
                            return v___x_1967_;
                        }
                        1 => {
                            v_node_1968_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                            v___x_1969_ = lean_usize_shift_right(v_x_1957_, v___x_1961_);
                            v_x_1956_ = v_node_1968_;
                            v_x_1957_ = v___x_1969_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1971_ = 0;
                            return v___x_1971_;
                        }
                    }
                } else {
                    v_ks_1972_ = crate::leanh::lean_ctor_get(v_x_1956_, 0);
                    v___x_1973_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1974_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_ks_1972_, v___x_1973_, v_x_1958_);
                    return v___x_1974_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___boxed(
    mut v_x_1975_: *mut crate::leanh::LeanObject,
    mut v_x_1976_: *mut crate::leanh::LeanObject,
    mut v_x_1977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_253__boxed_1978_: usize = 0;
    let mut v_res_1979_: u8 = 0;
    let mut v_r_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_253__boxed_1978_ = crate::leanh::lean_unbox_usize(v_x_1976_);
    crate::leanh::lean_dec(v_x_1976_);
    v_res_1979_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_1975_, v_x_253__boxed_1978_, v_x_1977_);
    crate::leanh::lean_dec(v_x_1977_);
    crate::leanh::lean_dec_ref(v_x_1975_);
    v_r_1980_ = crate::leanh::lean_box((v_res_1979_) as usize);
    return v_r_1980_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: u64 = 0;
    v___x_1981_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1982_ = lean_uint64_of_nat(v___x_1981_);
    return v___x_1982_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(
    mut v_x_1983_: *mut crate::leanh::LeanObject,
    mut v_x_1984_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_1986_: u64 = 0;
    let mut v___x_1987_: usize = 0;
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: u64 = 0;
    let mut v_hash_1990_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1984_) == 0 {
                    v___x_1989_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0);
                    v___y_1986_ = v___x_1989_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1990_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_1984_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1986_ = v_hash_1990_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1987_ = lean_uint64_to_usize(v___y_1986_);
                v___x_1988_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_1983_, v___x_1987_, v_x_1984_);
                return v___x_1988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___boxed(
    mut v_x_1991_: *mut crate::leanh::LeanObject,
    mut v_x_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1993_: u8 = 0;
    let mut v_r_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1993_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v_x_1991_, v_x_1992_);
    crate::leanh::lean_dec(v_x_1992_);
    crate::leanh::lean_dec_ref(v_x_1991_);
    v_r_1994_ = crate::leanh::lean_box((v_res_1993_) as usize);
    return v_r_1994_;
}
pub unsafe fn l_Lean_Server_existsBuiltinRpcProcedure(
    mut v_method_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
    v___x_1998_ = lean_st_ref_get(v___x_1997_);
    v___x_1999_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_1998_, v_method_1995_);
    crate::leanh::lean_dec(v___x_1998_);
    v___x_2000_ = crate::leanh::lean_box((v___x_1999_) as usize);
    v___x_2001_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2001_, 0, v___x_2000_);
    return v___x_2001_;
}
pub unsafe fn l_Lean_Server_existsBuiltinRpcProcedure___boxed(
    mut v_method_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2004_ = l_Lean_Server_existsBuiltinRpcProcedure(v_method_2002_);
    crate::leanh::lean_dec(v_method_2002_);
    return v_res_2004_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(
    mut v_00_u03b2_2005_: *mut crate::leanh::LeanObject,
    mut v_x_2006_: *mut crate::leanh::LeanObject,
    mut v_x_2007_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2008_: u8 = 0;
    v___x_2008_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v_x_2006_, v_x_2007_);
    return v___x_2008_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___boxed(
    mut v_00_u03b2_2009_: *mut crate::leanh::LeanObject,
    mut v_x_2010_: *mut crate::leanh::LeanObject,
    mut v_x_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2012_: u8 = 0;
    let mut v_r_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2012_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0(
            v_00_u03b2_2009_,
            v_x_2010_,
            v_x_2011_,
        );
    crate::leanh::lean_dec(v_x_2011_);
    crate::leanh::lean_dec_ref(v_x_2010_);
    v_r_2013_ = crate::leanh::lean_box((v_res_2012_) as usize);
    return v_r_2013_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(
    mut v_00_u03b2_2014_: *mut crate::leanh::LeanObject,
    mut v_x_2015_: *mut crate::leanh::LeanObject,
    mut v_x_2016_: usize,
    mut v_x_2017_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2018_: u8 = 0;
    v___x_2018_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg(v_x_2015_, v_x_2016_, v_x_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___boxed(
    mut v_00_u03b2_2019_: *mut crate::leanh::LeanObject,
    mut v_x_2020_: *mut crate::leanh::LeanObject,
    mut v_x_2021_: *mut crate::leanh::LeanObject,
    mut v_x_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_343__boxed_2023_: usize = 0;
    let mut v_res_2024_: u8 = 0;
    let mut v_r_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_343__boxed_2023_ = crate::leanh::lean_unbox_usize(v_x_2021_);
    crate::leanh::lean_dec(v_x_2021_);
    v_res_2024_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0(v_00_u03b2_2019_, v_x_2020_, v_x_343__boxed_2023_, v_x_2022_);
    crate::leanh::lean_dec(v_x_2022_);
    crate::leanh::lean_dec_ref(v_x_2020_);
    v_r_2025_ = crate::leanh::lean_box((v_res_2024_) as usize);
    return v_r_2025_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2026_: *mut crate::leanh::LeanObject,
    mut v_keys_2027_: *mut crate::leanh::LeanObject,
    mut v_vals_2028_: *mut crate::leanh::LeanObject,
    mut v_heq_2029_: *mut crate::leanh::LeanObject,
    mut v_i_2030_: *mut crate::leanh::LeanObject,
    mut v_k_2031_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2032_: u8 = 0;
    v___x_2032_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___redArg(v_keys_2027_, v_i_2030_, v_k_2031_);
    return v___x_2032_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2033_: *mut crate::leanh::LeanObject,
    mut v_keys_2034_: *mut crate::leanh::LeanObject,
    mut v_vals_2035_: *mut crate::leanh::LeanObject,
    mut v_heq_2036_: *mut crate::leanh::LeanObject,
    mut v_i_2037_: *mut crate::leanh::LeanObject,
    mut v_k_2038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2039_: u8 = 0;
    let mut v_r_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0_spec__1(v_00_u03b2_2033_, v_keys_2034_, v_vals_2035_, v_heq_2036_, v_i_2037_, v_k_2038_);
    crate::leanh::lean_dec(v_k_2038_);
    crate::leanh::lean_dec_ref(v_vals_2035_);
    crate::leanh::lean_dec_ref(v_keys_2034_);
    v_r_2040_ = crate::leanh::lean_box((v_res_2039_) as usize);
    return v_r_2040_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(
    mut v___y_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_doc_2043_ = crate::leanh::lean_ctor_get(v___y_2041_, 1);
    crate::leanh::lean_inc_ref(v_doc_2043_);
    v___x_2044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2044_, 0, v_doc_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1___boxed(
    mut v___y_2045_: *mut crate::leanh::LeanObject,
    mut v___y_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2047_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v___y_2045_);
    crate::leanh::lean_dec_ref(v___y_2045_);
    return v_res_2047_;
}
pub unsafe fn l_Lean_Server_handleRpcCall___lam__0(
    mut v_val_2048_: *mut crate::leanh::LeanObject,
    mut v_sessionId_2049_: u64,
    mut v_params_2050_: *mut crate::leanh::LeanObject,
    mut v___y_2051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2058_: u8 = 0;
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2068_: u8 = 0;
    let mut v_a_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2072_: u8 = 0;
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2076_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2053_ = crate::leanh::lean_box_uint64(v_sessionId_2049_);
                crate::leanh::lean_inc_ref(v___y_2051_);
                v___x_2054_ = crate::leanh::lean_apply_4(
                    v_val_2048_,
                    v___x_2053_,
                    v_params_2050_,
                    v___y_2051_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2054_) == 0 {
                    v_a_2055_ = crate::leanh::lean_ctor_get(v___x_2054_, 0);
                    v_isSharedCheck_2068_ = (!crate::leanh::lean_is_exclusive(v___x_2054_)) as u8;
                    if v_isSharedCheck_2068_ == 0 {
                        v___x_2057_ = v___x_2054_;
                        v_isShared_2058_ = v_isSharedCheck_2068_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2055_);
                        crate::leanh::lean_dec(v___x_2054_);
                        v___x_2057_ = crate::leanh::lean_box(0);
                        v_isShared_2058_ = v_isSharedCheck_2068_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2069_ = crate::leanh::lean_ctor_get(v___x_2054_, 0);
                    v_isSharedCheck_2076_ = (!crate::leanh::lean_is_exclusive(v___x_2054_)) as u8;
                    if v_isSharedCheck_2076_ == 0 {
                        v___x_2071_ = v___x_2054_;
                        v_isShared_2072_ = v_isSharedCheck_2076_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2069_);
                        crate::leanh::lean_dec(v___x_2054_);
                        v___x_2071_ = crate::leanh::lean_box(0);
                        v_isShared_2072_ = v_isSharedCheck_2076_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2059_ = lean_io_wait(v_a_2055_);
                if crate::leanh::lean_obj_tag(v___x_2059_) == 0 {
                    v_a_2060_ = crate::leanh::lean_ctor_get(v___x_2059_, 0);
                    crate::leanh::lean_inc(v_a_2060_);
                    crate::leanh::lean_dec_ref_known(v___x_2059_, 1);
                    if v_isShared_2058_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2057_, 1);
                        crate::leanh::lean_ctor_set(v___x_2057_, 0, v_a_2060_);
                        v___x_2062_ = v___x_2057_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2060_);
                        v___x_2062_ = v_reuseFailAlloc_2063_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2064_ = crate::leanh::lean_ctor_get(v___x_2059_, 0);
                    crate::leanh::lean_inc(v_a_2064_);
                    crate::leanh::lean_dec_ref_known(v___x_2059_, 1);
                    if v_isShared_2058_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2057_, 0, v_a_2064_);
                        v___x_2066_ = v___x_2057_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2067_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2064_);
                        v___x_2066_ = v_reuseFailAlloc_2067_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2062_;
            }
            3 => {
                return v___x_2066_;
            }
            4 => {
                if v_isShared_2072_ == 0 {
                    v___x_2074_ = v___x_2071_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
                    v___x_2074_ = v_reuseFailAlloc_2075_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2074_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_handleRpcCall___lam__0___boxed(
    mut v_val_2077_: *mut crate::leanh::LeanObject,
    mut v_sessionId_2078_: *mut crate::leanh::LeanObject,
    mut v_params_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sessionId_boxed_2082_: u64 = 0;
    let mut v_res_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sessionId_boxed_2082_ = crate::leanh::lean_unbox_uint64(v_sessionId_2078_);
    crate::leanh::lean_dec_ref(v_sessionId_2078_);
    v_res_2083_ = l_Lean_Server_handleRpcCall___lam__0(
        v_val_2077_,
        v_sessionId_boxed_2082_,
        v_params_2079_,
        v___y_2080_,
    );
    crate::leanh::lean_dec_ref(v___y_2080_);
    return v_res_2083_;
}
pub unsafe fn l_Lean_Server_handleRpcCall___lam__1(
    mut v___x_2084_: *mut crate::leanh::LeanObject,
    mut v___x_2085_: *mut crate::leanh::LeanObject,
    mut v_method_2086_: *mut crate::leanh::LeanObject,
    mut v_s_2087_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: u8 = 0;
    v___x_2088_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_2087_);
    v___x_2089_ = lean_nat_dec_le(v___x_2084_, v___x_2088_);
    crate::leanh::lean_dec(v___x_2088_);
    if v___x_2089_ == 0 {
        let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toEnvExtension_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: u8 = 0;
        let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2090_ = l_Lean_Server_userRpcProcedures;
        v_toEnvExtension_2091_ = crate::leanh::lean_ctor_get(v___x_2090_, 0);
        v_asyncMode_2092_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2091_, 2);
        v___x_2093_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_2087_);
        v___x_2094_ = 0;
        v___x_2095_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
            v___x_2085_,
            v___x_2090_,
            v___x_2093_,
            v_method_2086_,
            v_asyncMode_2092_,
            v___x_2094_,
        );
        if crate::leanh::lean_obj_tag(v___x_2095_) == 0 {
            return v___x_2089_;
        } else {
            let mut v___x_2096_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v___x_2095_, 1);
            v___x_2096_ = 1;
            return v___x_2096_;
        }
    } else {
        crate::leanh::lean_dec(v_method_2086_);
        crate::leanh::lean_dec(v___x_2085_);
        return v___x_2089_;
    }
}
pub unsafe fn l_Lean_Server_handleRpcCall___lam__1___boxed(
    mut v___x_2097_: *mut crate::leanh::LeanObject,
    mut v___x_2098_: *mut crate::leanh::LeanObject,
    mut v_method_2099_: *mut crate::leanh::LeanObject,
    mut v_s_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2101_: u8 = 0;
    let mut v_r_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ =
        l_Lean_Server_handleRpcCall___lam__1(v___x_2097_, v___x_2098_, v_method_2099_, v_s_2100_);
    crate::leanh::lean_dec_ref(v_s_2100_);
    crate::leanh::lean_dec(v___x_2097_);
    v_r_2102_ = crate::leanh::lean_box((v_res_2101_) as usize);
    return v_r_2102_;
}
pub unsafe fn l_Lean_Server_handleRpcCall___lam__2(
    mut v___x_2103_: *mut crate::leanh::LeanObject,
    mut v___y_2104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2106_, 0, v___x_2103_);
    return v___x_2106_;
}
pub unsafe fn l_Lean_Server_handleRpcCall___lam__2___boxed(
    mut v___x_2107_: *mut crate::leanh::LeanObject,
    mut v___y_2108_: *mut crate::leanh::LeanObject,
    mut v___y_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2110_ = l_Lean_Server_handleRpcCall___lam__2(v___x_2107_, v___y_2108_);
    crate::leanh::lean_dec_ref(v___y_2108_);
    return v_res_2110_;
}
pub unsafe fn l_Lean_Server_handleRpcCall___lam__3(
    mut v___x_2113_: *mut crate::leanh::LeanObject,
    mut v_method_2114_: *mut crate::leanh::LeanObject,
    mut v___x_2115_: *mut crate::leanh::LeanObject,
    mut v___x_2116_: u8,
    mut v_sessionId_2117_: u64,
    mut v_params_2118_: *mut crate::leanh::LeanObject,
    mut v___x_2119_: *mut crate::leanh::LeanObject,
    mut v_snap_2120_: *mut crate::leanh::LeanObject,
    mut v___y_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u8 = 0;
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdState_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2138_: u8 = 0;
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_a_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2123_ = l_Lean_Server_userRpcProcedures;
                v_toEnvExtension_2124_ = crate::leanh::lean_ctor_get(v___x_2123_, 0);
                v_asyncMode_2125_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2124_, 2);
                v___x_2126_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_2120_);
                v___x_2127_ = 0;
                crate::leanh::lean_inc_ref(v___x_2126_);
                v___x_2128_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                    v___x_2113_,
                    v___x_2123_,
                    v___x_2126_,
                    v_method_2114_,
                    v_asyncMode_2125_,
                    v___x_2127_,
                );
                if crate::leanh::lean_obj_tag(v___x_2128_) == 1 {
                    crate::leanh::lean_dec_ref(v___x_2119_);
                    v_cmdState_2129_ = crate::leanh::lean_ctor_get(v_snap_2120_, 2);
                    v_val_2130_ = crate::leanh::lean_ctor_get(v___x_2128_, 0);
                    crate::leanh::lean_inc_n(v_val_2130_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2128_, 1);
                    v_scopes_2131_ = crate::leanh::lean_ctor_get(v_cmdState_2129_, 2);
                    v___x_2132_ = l_List_head_x21___redArg(v___x_2115_, v_scopes_2131_);
                    v_opts_2133_ = crate::leanh::lean_ctor_get(v___x_2132_, 1);
                    crate::leanh::lean_inc_ref(v_opts_2133_);
                    crate::leanh::lean_dec(v___x_2132_);
                    v___x_2134_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe(v___x_2126_, v_opts_2133_, v_val_2130_);
                    crate::leanh::lean_dec_ref(v_opts_2133_);
                    if crate::leanh::lean_obj_tag(v___x_2134_) == 0 {
                        crate::leanh::lean_dec(v_params_2118_);
                        v_a_2135_ = crate::leanh::lean_ctor_get(v___x_2134_, 0);
                        v_isSharedCheck_2150_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2134_)) as u8;
                        if v_isSharedCheck_2150_ == 0 {
                            v___x_2137_ = v___x_2134_;
                            v_isShared_2138_ = v_isSharedCheck_2150_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2135_);
                            crate::leanh::lean_dec(v___x_2134_);
                            v___x_2137_ = crate::leanh::lean_box(0);
                            v_isShared_2138_ = v_isSharedCheck_2150_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2130_);
                        v_a_2151_ = crate::leanh::lean_ctor_get(v___x_2134_, 0);
                        crate::leanh::lean_inc(v_a_2151_);
                        crate::leanh::lean_dec_ref_known(v___x_2134_, 1);
                        v___x_2152_ = crate::leanh::lean_box_uint64(v_sessionId_2117_);
                        crate::leanh::lean_inc_ref(v___y_2121_);
                        v___x_2153_ = crate::leanh::lean_apply_4(
                            v_a_2151_,
                            v___x_2152_,
                            v_params_2118_,
                            v___y_2121_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_2153_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2128_);
                    crate::leanh::lean_dec_ref(v___x_2126_);
                    crate::leanh::lean_dec(v_params_2118_);
                    v___x_2154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2154_, 0, v___x_2119_);
                    return v___x_2154_;
                }
            }
            1 => {
                v___x_2139_ = 4;
                v___x_2140_ = l_Lean_Server_handleRpcCall___lam__3___closed__0;
                v___x_2141_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_val_2130_,
                    v___x_2116_,
                );
                v___x_2142_ = lean_string_append(v___x_2140_, v___x_2141_);
                crate::leanh::lean_dec_ref(v___x_2141_);
                v___x_2143_ = l_Lean_Server_handleRpcCall___lam__3___closed__1;
                v___x_2144_ = lean_string_append(v___x_2142_, v___x_2143_);
                v___x_2145_ = lean_string_append(v___x_2144_, v_a_2135_);
                crate::leanh::lean_dec(v_a_2135_);
                v___x_2146_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2146_, 0, v___x_2145_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2146_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2139_,
                );
                if v_isShared_2138_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2137_, 1);
                    crate::leanh::lean_ctor_set(v___x_2137_, 0, v___x_2146_);
                    v___x_2148_ = v___x_2137_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_handleRpcCall___lam__3___boxed(
    mut v___x_2155_: *mut crate::leanh::LeanObject,
    mut v_method_2156_: *mut crate::leanh::LeanObject,
    mut v___x_2157_: *mut crate::leanh::LeanObject,
    mut v___x_2158_: *mut crate::leanh::LeanObject,
    mut v_sessionId_2159_: *mut crate::leanh::LeanObject,
    mut v_params_2160_: *mut crate::leanh::LeanObject,
    mut v___x_2161_: *mut crate::leanh::LeanObject,
    mut v_snap_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2331__boxed_2165_: u8 = 0;
    let mut v_sessionId_boxed_2166_: u64 = 0;
    let mut v_res_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2331__boxed_2165_ = (crate::leanh::lean_unbox(v___x_2158_) as u8);
    v_sessionId_boxed_2166_ = crate::leanh::lean_unbox_uint64(v_sessionId_2159_);
    crate::leanh::lean_dec_ref(v_sessionId_2159_);
    v_res_2167_ = l_Lean_Server_handleRpcCall___lam__3(
        v___x_2155_,
        v_method_2156_,
        v___x_2157_,
        v___x_2331__boxed_2165_,
        v_sessionId_boxed_2166_,
        v_params_2160_,
        v___x_2161_,
        v_snap_2162_,
        v___y_2163_,
    );
    crate::leanh::lean_dec_ref(v___y_2163_);
    crate::leanh::lean_dec_ref(v_snap_2162_);
    crate::leanh::lean_dec_ref(v___x_2157_);
    return v_res_2167_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(
    mut v_keys_2168_: *mut crate::leanh::LeanObject,
    mut v_vals_2169_: *mut crate::leanh::LeanObject,
    mut v_i_2170_: *mut crate::leanh::LeanObject,
    mut v_k_2171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2172_ = lean_array_get_size(v_keys_2168_);
                v___x_2173_ = lean_nat_dec_lt(v_i_2170_, v___x_2172_);
                if v___x_2173_ == 0 {
                    crate::leanh::lean_dec(v_i_2170_);
                    v___x_2174_ = crate::leanh::lean_box(0);
                    return v___x_2174_;
                } else {
                    v_k_x27_2175_ = lean_array_fget_borrowed(v_keys_2168_, v_i_2170_);
                    v___x_2176_ = lean_name_eq(v_k_2171_, v_k_x27_2175_);
                    if v___x_2176_ == 0 {
                        v___x_2177_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2178_ = lean_nat_add(v_i_2170_, v___x_2177_);
                        crate::leanh::lean_dec(v_i_2170_);
                        v_i_2170_ = v___x_2178_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2180_ = lean_array_fget_borrowed(v_vals_2169_, v_i_2170_);
                        crate::leanh::lean_dec(v_i_2170_);
                        crate::leanh::lean_inc(v___x_2180_);
                        v___x_2181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2181_, 0, v___x_2180_);
                        return v___x_2181_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_keys_2182_: *mut crate::leanh::LeanObject,
    mut v_vals_2183_: *mut crate::leanh::LeanObject,
    mut v_i_2184_: *mut crate::leanh::LeanObject,
    mut v_k_2185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2186_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_2182_, v_vals_2183_, v_i_2184_, v_k_2185_);
    crate::leanh::lean_dec(v_k_2185_);
    crate::leanh::lean_dec_ref(v_vals_2183_);
    crate::leanh::lean_dec_ref(v_keys_2182_);
    return v_res_2186_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(
    mut v_x_2187_: *mut crate::leanh::LeanObject,
    mut v_x_2188_: usize,
    mut v_x_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: usize = 0;
    let mut v___x_2193_: usize = 0;
    let mut v___x_2194_: usize = 0;
    let mut v_j_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u8 = 0;
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: usize = 0;
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2187_) == 0 {
                    v_es_2190_ = crate::leanh::lean_ctor_get(v_x_2187_, 0);
                    v___x_2191_ = crate::leanh::lean_box(2);
                    v___x_2192_ = 5usize;
                    v___x_2193_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
                    v___x_2194_ = lean_usize_land(v_x_2188_, v___x_2193_);
                    v_j_2195_ = lean_usize_to_nat(v___x_2194_);
                    v___x_2196_ = lean_array_get_borrowed(v___x_2191_, v_es_2190_, v_j_2195_);
                    crate::leanh::lean_dec(v_j_2195_);
                    match crate::leanh::lean_obj_tag(v___x_2196_) {
                        0 => {
                            v_key_2197_ = crate::leanh::lean_ctor_get(v___x_2196_, 0);
                            v_val_2198_ = crate::leanh::lean_ctor_get(v___x_2196_, 1);
                            v___x_2199_ = lean_name_eq(v_x_2189_, v_key_2197_);
                            if v___x_2199_ == 0 {
                                v___x_2200_ = crate::leanh::lean_box(0);
                                return v___x_2200_;
                            } else {
                                crate::leanh::lean_inc(v_val_2198_);
                                v___x_2201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2201_, 0, v_val_2198_);
                                return v___x_2201_;
                            }
                        }
                        1 => {
                            v_node_2202_ = crate::leanh::lean_ctor_get(v___x_2196_, 0);
                            v___x_2203_ = lean_usize_shift_right(v_x_2188_, v___x_2192_);
                            v_x_2187_ = v_node_2202_;
                            v_x_2188_ = v___x_2203_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2205_ = crate::leanh::lean_box(0);
                            return v___x_2205_;
                        }
                    }
                } else {
                    v_ks_2206_ = crate::leanh::lean_ctor_get(v_x_2187_, 0);
                    v_vs_2207_ = crate::leanh::lean_ctor_get(v_x_2187_, 1);
                    v___x_2208_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2209_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_ks_2206_, v_vs_2207_, v___x_2208_, v_x_2189_);
                    return v___x_2209_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg___boxed(
    mut v_x_2210_: *mut crate::leanh::LeanObject,
    mut v_x_2211_: *mut crate::leanh::LeanObject,
    mut v_x_2212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2428__boxed_2213_: usize = 0;
    let mut v_res_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2428__boxed_2213_ = crate::leanh::lean_unbox_usize(v_x_2211_);
    crate::leanh::lean_dec(v_x_2211_);
    v_res_2214_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_2210_, v_x_2428__boxed_2213_, v_x_2212_);
    crate::leanh::lean_dec(v_x_2212_);
    crate::leanh::lean_dec_ref(v_x_2210_);
    return v_res_2214_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(
    mut v_x_2215_: *mut crate::leanh::LeanObject,
    mut v_x_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2218_: u64 = 0;
    let mut v___x_2219_: usize = 0;
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u64 = 0;
    let mut v_hash_2222_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2216_) == 0 {
                    v___x_2221_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg___closed__0);
                    v___y_2218_ = v___x_2221_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2222_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_2216_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2218_ = v_hash_2222_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2219_ = lean_uint64_to_usize(v___y_2218_);
                v___x_2220_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_2215_, v___x_2219_, v_x_2216_);
                return v___x_2220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg___boxed(
    mut v_x_2223_: *mut crate::leanh::LeanObject,
    mut v_x_2224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2225_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(
            v_x_2223_, v_x_2224_,
        );
    crate::leanh::lean_dec(v_x_2224_);
    crate::leanh::lean_dec_ref(v_x_2223_);
    return v_res_2225_;
}
pub unsafe fn l_Lean_Server_handleRpcCall(
    mut v_p_2228_: *mut crate::leanh::LeanObject,
    mut v_a_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTextDocumentPositionParams_2233_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sessionId_2234_: u64 = 0;
    let mut v_method_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2231_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
    v___x_2232_ = lean_st_ref_get(v___x_2231_);
    v_toTextDocumentPositionParams_2233_ = crate::leanh::lean_ctor_get(v_p_2228_, 0);
    crate::leanh::lean_inc_ref(v_toTextDocumentPositionParams_2233_);
    v_sessionId_2234_ = crate::leanh::lean_ctor_get_uint64(
        v_p_2228_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v_method_2235_ = crate::leanh::lean_ctor_get(v_p_2228_, 1);
    crate::leanh::lean_inc(v_method_2235_);
    v_params_2236_ = crate::leanh::lean_ctor_get(v_p_2228_, 2);
    crate::leanh::lean_inc(v_params_2236_);
    crate::leanh::lean_dec_ref(v_p_2228_);
    v___x_2237_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(
            v___x_2232_,
            v_method_2235_,
        );
    crate::leanh::lean_dec(v___x_2232_);
    if crate::leanh::lean_obj_tag(v___x_2237_) == 1 {
        let mut v_val_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_method_2235_);
        crate::leanh::lean_dec_ref(v_toTextDocumentPositionParams_2233_);
        v_val_2238_ = crate::leanh::lean_ctor_get(v___x_2237_, 0);
        crate::leanh::lean_inc(v_val_2238_);
        crate::leanh::lean_dec_ref_known(v___x_2237_, 1);
        v___x_2239_ = crate::leanh::lean_box_uint64(v_sessionId_2234_);
        v___f_2240_ = crate::leanh::lean_alloc_closure(
            l_Lean_Server_handleRpcCall___lam__0___boxed as *mut core::ffi::c_void,
            5,
            3,
        );
        crate::leanh::lean_closure_set(v___f_2240_, 0, v_val_2238_);
        crate::leanh::lean_closure_set(v___f_2240_, 1, v___x_2239_);
        crate::leanh::lean_closure_set(v___f_2240_, 2, v_params_2236_);
        v___x_2241_ = l_Lean_Server_RequestM_asTask___redArg(v___f_2240_, v_a_2229_);
        return v___x_2241_;
    } else {
        let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toEditableDocumentCore_2244_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v_meta_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_text_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_position_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: u8 = 0;
        let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2254_: u8 = 0;
        let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2237_);
        v___x_2242_ =
            l_Lean_Server_RequestM_readDoc___at___00Lean_Server_handleRpcCall_spec__1(v_a_2229_);
        v_a_2243_ = crate::leanh::lean_ctor_get(v___x_2242_, 0);
        crate::leanh::lean_inc(v_a_2243_);
        crate::leanh::lean_dec_ref(v___x_2242_);
        v_toEditableDocumentCore_2244_ = crate::leanh::lean_ctor_get(v_a_2243_, 0);
        v_meta_2245_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_2244_, 0);
        v_text_2246_ = crate::leanh::lean_ctor_get(v_meta_2245_, 3);
        v_position_2247_ = crate::leanh::lean_ctor_get(v_toTextDocumentPositionParams_2233_, 1);
        crate::leanh::lean_inc_ref(v_position_2247_);
        crate::leanh::lean_dec_ref(v_toTextDocumentPositionParams_2233_);
        v___x_2248_ = crate::leanh::lean_box(0);
        v___x_2249_ = l_Lean_Elab_Command_instInhabitedScope_default;
        v___x_2250_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2246_, v_position_2247_);
        crate::leanh::lean_inc_n(v_method_2235_, 2);
        v___f_2251_ = crate::leanh::lean_alloc_closure(
            l_Lean_Server_handleRpcCall___lam__1___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_2251_, 0, v___x_2250_);
        crate::leanh::lean_closure_set(v___f_2251_, 1, v___x_2248_);
        crate::leanh::lean_closure_set(v___f_2251_, 2, v_method_2235_);
        v___x_2252_ = 2;
        v___x_2253_ = l_Lean_Server_handleRpcCall___closed__0;
        v___x_2254_ = 1;
        v___x_2255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_method_2235_,
            v___x_2254_,
        );
        v___x_2256_ = lean_string_append(v___x_2253_, v___x_2255_);
        crate::leanh::lean_dec_ref(v___x_2255_);
        v___x_2257_ = l_Lean_Server_handleRpcCall___closed__1;
        v___x_2258_ = lean_string_append(v___x_2256_, v___x_2257_);
        v___x_2259_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_2259_, 0, v___x_2258_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_2259_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_2252_,
        );
        crate::leanh::lean_inc_ref(v___x_2259_);
        v___f_2260_ = crate::leanh::lean_alloc_closure(
            l_Lean_Server_handleRpcCall___lam__2___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2260_, 0, v___x_2259_);
        v___x_2261_ = crate::leanh::lean_box((v___x_2254_) as usize);
        v___x_2262_ = crate::leanh::lean_box_uint64(v_sessionId_2234_);
        v___f_2263_ = crate::leanh::lean_alloc_closure(
            l_Lean_Server_handleRpcCall___lam__3___boxed as *mut core::ffi::c_void,
            10,
            7,
        );
        crate::leanh::lean_closure_set(v___f_2263_, 0, v___x_2248_);
        crate::leanh::lean_closure_set(v___f_2263_, 1, v_method_2235_);
        crate::leanh::lean_closure_set(v___f_2263_, 2, v___x_2249_);
        crate::leanh::lean_closure_set(v___f_2263_, 3, v___x_2261_);
        crate::leanh::lean_closure_set(v___f_2263_, 4, v___x_2262_);
        crate::leanh::lean_closure_set(v___f_2263_, 5, v_params_2236_);
        crate::leanh::lean_closure_set(v___f_2263_, 6, v___x_2259_);
        v___x_2264_ = l_Lean_Server_RequestM_bindWaitFindSnap___redArg(
            v_a_2243_,
            v___f_2251_,
            v___f_2260_,
            v___f_2263_,
            v_a_2229_,
        );
        return v___x_2264_;
    }
}
pub unsafe fn l_Lean_Server_handleRpcCall___boxed(
    mut v_p_2265_: *mut crate::leanh::LeanObject,
    mut v_a_2266_: *mut crate::leanh::LeanObject,
    mut v_a_2267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Lean_Server_handleRpcCall(v_p_2265_, v_a_2266_);
    crate::leanh::lean_dec_ref(v_a_2266_);
    return v_res_2268_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(
    mut v_00_u03b2_2269_: *mut crate::leanh::LeanObject,
    mut v_x_2270_: *mut crate::leanh::LeanObject,
    mut v_x_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2272_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___redArg(
            v_x_2270_, v_x_2271_,
        );
    return v___x_2272_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0___boxed(
    mut v_00_u03b2_2273_: *mut crate::leanh::LeanObject,
    mut v_x_2274_: *mut crate::leanh::LeanObject,
    mut v_x_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0(
        v_00_u03b2_2273_,
        v_x_2274_,
        v_x_2275_,
    );
    crate::leanh::lean_dec(v_x_2275_);
    crate::leanh::lean_dec_ref(v_x_2274_);
    return v_res_2276_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(
    mut v_00_u03b2_2277_: *mut crate::leanh::LeanObject,
    mut v_x_2278_: *mut crate::leanh::LeanObject,
    mut v_x_2279_: usize,
    mut v_x_2280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2281_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___redArg(v_x_2278_, v_x_2279_, v_x_2280_);
    return v___x_2281_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0___boxed(
    mut v_00_u03b2_2282_: *mut crate::leanh::LeanObject,
    mut v_x_2283_: *mut crate::leanh::LeanObject,
    mut v_x_2284_: *mut crate::leanh::LeanObject,
    mut v_x_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2566__boxed_2286_: usize = 0;
    let mut v_res_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2566__boxed_2286_ = crate::leanh::lean_unbox_usize(v_x_2284_);
    crate::leanh::lean_dec(v_x_2284_);
    v_res_2287_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0(v_00_u03b2_2282_, v_x_2283_, v_x_2566__boxed_2286_, v_x_2285_);
    crate::leanh::lean_dec(v_x_2285_);
    crate::leanh::lean_dec_ref(v_x_2283_);
    return v_res_2287_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2288_: *mut crate::leanh::LeanObject,
    mut v_keys_2289_: *mut crate::leanh::LeanObject,
    mut v_vals_2290_: *mut crate::leanh::LeanObject,
    mut v_heq_2291_: *mut crate::leanh::LeanObject,
    mut v_i_2292_: *mut crate::leanh::LeanObject,
    mut v_k_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___redArg(v_keys_2289_, v_vals_2290_, v_i_2292_, v_k_2293_);
    return v___x_2294_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2295_: *mut crate::leanh::LeanObject,
    mut v_keys_2296_: *mut crate::leanh::LeanObject,
    mut v_vals_2297_: *mut crate::leanh::LeanObject,
    mut v_heq_2298_: *mut crate::leanh::LeanObject,
    mut v_i_2299_: *mut crate::leanh::LeanObject,
    mut v_k_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_handleRpcCall_spec__0_spec__0_spec__2(v_00_u03b2_2295_, v_keys_2296_, v_vals_2297_, v_heq_2298_, v_i_2299_, v_k_2300_);
    crate::leanh::lean_dec(v_k_2300_);
    crate::leanh::lean_dec_ref(v_vals_2297_);
    crate::leanh::lean_dec_ref(v_keys_2296_);
    return v_res_2301_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(
    mut v_serialize_x3f_2302_: *mut crate::leanh::LeanObject,
    mut v_a_2303_: u8,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_a_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v_val_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2324_: u8 = 0;
    let mut v_a_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2328_: u8 = 0;
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___y_2304_) == 0 {
                    crate::leanh::lean_dec(v_serialize_x3f_2302_);
                    v_a_2305_ = crate::leanh::lean_ctor_get(v___y_2304_, 0);
                    v_isSharedCheck_2312_ = (!crate::leanh::lean_is_exclusive(v___y_2304_)) as u8;
                    if v_isSharedCheck_2312_ == 0 {
                        v___x_2307_ = v___y_2304_;
                        v_isShared_2308_ = v_isSharedCheck_2312_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2305_);
                        crate::leanh::lean_dec(v___y_2304_);
                        v___x_2307_ = crate::leanh::lean_box(0);
                        v_isShared_2308_ = v_isSharedCheck_2312_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_serialize_x3f_2302_) == 1 {
                        v_a_2313_ = crate::leanh::lean_ctor_get(v___y_2304_, 0);
                        v_isSharedCheck_2324_ =
                            (!crate::leanh::lean_is_exclusive(v___y_2304_)) as u8;
                        if v_isSharedCheck_2324_ == 0 {
                            v___x_2315_ = v___y_2304_;
                            v_isShared_2316_ = v_isSharedCheck_2324_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2313_);
                            crate::leanh::lean_dec(v___y_2304_);
                            v___x_2315_ = crate::leanh::lean_box(0);
                            v_isShared_2316_ = v_isSharedCheck_2324_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_serialize_x3f_2302_);
                        v_a_2325_ = crate::leanh::lean_ctor_get(v___y_2304_, 0);
                        v_isSharedCheck_2335_ =
                            (!crate::leanh::lean_is_exclusive(v___y_2304_)) as u8;
                        if v_isSharedCheck_2335_ == 0 {
                            v___x_2327_ = v___y_2304_;
                            v_isShared_2328_ = v_isSharedCheck_2335_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2325_);
                            crate::leanh::lean_dec(v___y_2304_);
                            v___x_2327_ = crate::leanh::lean_box(0);
                            v_isShared_2328_ = v_isSharedCheck_2335_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2308_ == 0 {
                    v___x_2310_ = v___x_2307_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
                    v___x_2310_ = v_reuseFailAlloc_2311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2310_;
            }
            3 => {
                v_val_2317_ = crate::leanh::lean_ctor_get(v_serialize_x3f_2302_, 0);
                crate::leanh::lean_inc(v_val_2317_);
                crate::leanh::lean_dec_ref_known(v_serialize_x3f_2302_, 1);
                v___x_2318_ = crate::leanh::lean_box(0);
                v___x_2319_ = crate::leanh::lean_apply_1(v_val_2317_, v_a_2313_);
                v___x_2320_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2320_, 0, v___x_2318_);
                crate::leanh::lean_ctor_set(v___x_2320_, 1, v___x_2319_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2320_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_a_2303_,
                );
                if v_isShared_2316_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2315_, 0, v___x_2320_);
                    v___x_2322_ = v___x_2315_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2323_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
                    v___x_2322_ = v_reuseFailAlloc_2323_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2322_;
            }
            5 => {
                crate::leanh::lean_inc(v_a_2325_);
                v___x_2329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2329_, 0, v_a_2325_);
                v___x_2330_ = l_Lean_Json_compress(v_a_2325_);
                v___x_2331_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2331_, 0, v___x_2329_);
                crate::leanh::lean_ctor_set(v___x_2331_, 1, v___x_2330_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2331_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_a_2303_,
                );
                if v_isShared_2328_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2327_, 0, v___x_2331_);
                    v___x_2333_ = v___x_2327_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2334_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
                    v___x_2333_ = v_reuseFailAlloc_2334_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v_serialize_x3f_2336_: *mut crate::leanh::LeanObject,
    mut v_a_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_666__boxed_2339_: u8 = 0;
    let mut v_res_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_666__boxed_2339_ = (crate::leanh::lean_unbox(v_a_2337_) as u8);
    v_res_2340_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1(v_serialize_x3f_2336_, v_a_666__boxed_2339_, v___y_2338_);
    return v_res_2340_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(
    mut v_x_2341_: *mut crate::leanh::LeanObject,
    mut v_x_2342_: *mut crate::leanh::LeanObject,
    mut v_x_2343_: *mut crate::leanh::LeanObject,
    mut v_x_2344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: u8 = 0;
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2345_ = crate::leanh::lean_ctor_get(v_x_2341_, 0);
                v_vs_2346_ = crate::leanh::lean_ctor_get(v_x_2341_, 1);
                v_isSharedCheck_2370_ = (!crate::leanh::lean_is_exclusive(v_x_2341_)) as u8;
                if v_isSharedCheck_2370_ == 0 {
                    v___x_2348_ = v_x_2341_;
                    v_isShared_2349_ = v_isSharedCheck_2370_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2346_);
                    crate::leanh::lean_inc(v_ks_2345_);
                    crate::leanh::lean_dec(v_x_2341_);
                    v___x_2348_ = crate::leanh::lean_box(0);
                    v_isShared_2349_ = v_isSharedCheck_2370_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2350_ = lean_array_get_size(v_ks_2345_);
                v___x_2351_ = lean_nat_dec_lt(v_x_2342_, v___x_2350_);
                if v___x_2351_ == 0 {
                    crate::leanh::lean_dec(v_x_2342_);
                    v___x_2352_ = lean_array_push(v_ks_2345_, v_x_2343_);
                    v___x_2353_ = lean_array_push(v_vs_2346_, v_x_2344_);
                    if v_isShared_2349_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2348_, 1, v___x_2353_);
                        crate::leanh::lean_ctor_set(v___x_2348_, 0, v___x_2352_);
                        v___x_2355_ = v___x_2348_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2356_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2352_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 1, v___x_2353_);
                        v___x_2355_ = v_reuseFailAlloc_2356_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2357_ = lean_array_fget_borrowed(v_ks_2345_, v_x_2342_);
                    v___x_2358_ = lean_string_dec_eq(v_x_2343_, v_k_x27_2357_);
                    if v___x_2358_ == 0 {
                        if v_isShared_2349_ == 0 {
                            v___x_2360_ = v___x_2348_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2364_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_ks_2345_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_vs_2346_);
                            v___x_2360_ = v_reuseFailAlloc_2364_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2365_ = lean_array_fset(v_ks_2345_, v_x_2342_, v_x_2343_);
                        v___x_2366_ = lean_array_fset(v_vs_2346_, v_x_2342_, v_x_2344_);
                        crate::leanh::lean_dec(v_x_2342_);
                        if v_isShared_2349_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2348_, 1, v___x_2366_);
                            crate::leanh::lean_ctor_set(v___x_2348_, 0, v___x_2365_);
                            v___x_2368_ = v___x_2348_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2369_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2365_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2366_);
                            v___x_2368_ = v_reuseFailAlloc_2369_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2355_;
            }
            3 => {
                v___x_2361_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2362_ = lean_nat_add(v_x_2342_, v___x_2361_);
                crate::leanh::lean_dec(v_x_2342_);
                v_x_2341_ = v___x_2360_;
                v_x_2342_ = v___x_2362_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(
    mut v_n_2371_: *mut crate::leanh::LeanObject,
    mut v_k_2372_: *mut crate::leanh::LeanObject,
    mut v_v_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2374_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2375_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_n_2371_, v___x_2374_, v_k_2372_, v_v_2373_);
    return v___x_2375_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2376_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(
    mut v_x_2377_: *mut crate::leanh::LeanObject,
    mut v_x_2378_: usize,
    mut v_x_2379_: usize,
    mut v_x_2380_: *mut crate::leanh::LeanObject,
    mut v_x_2381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: usize = 0;
    let mut v___x_2384_: usize = 0;
    let mut v___x_2385_: usize = 0;
    let mut v___x_2386_: usize = 0;
    let mut v_j_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: u8 = 0;
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v_v_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v___x_2407_: u8 = 0;
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2413_: u8 = 0;
    let mut v_node_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2417_: u8 = 0;
    let mut v___x_2418_: usize = 0;
    let mut v___x_2419_: usize = 0;
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2424_: u8 = 0;
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2426_: u8 = 0;
    let mut v_unused_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2432_: u8 = 0;
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2437_: u8 = 0;
    let mut v_ks_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: usize = 0;
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v_reuseFailAlloc_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2449_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2377_) == 0 {
                    v_es_2382_ = crate::leanh::lean_ctor_get(v_x_2377_, 0);
                    v___x_2383_ = 5usize;
                    v___x_2384_ = 1usize;
                    v___x_2385_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
                    v___x_2386_ = lean_usize_land(v_x_2378_, v___x_2385_);
                    v_j_2387_ = lean_usize_to_nat(v___x_2386_);
                    v___x_2388_ = lean_array_get_size(v_es_2382_);
                    v___x_2389_ = lean_nat_dec_lt(v_j_2387_, v___x_2388_);
                    if v___x_2389_ == 0 {
                        crate::leanh::lean_dec(v_j_2387_);
                        crate::leanh::lean_dec(v_x_2381_);
                        crate::leanh::lean_dec_ref(v_x_2380_);
                        return v_x_2377_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2382_);
                        v_isSharedCheck_2426_ = (!crate::leanh::lean_is_exclusive(v_x_2377_)) as u8;
                        if v_isSharedCheck_2426_ == 0 {
                            v_unused_2427_ = crate::leanh::lean_ctor_get(v_x_2377_, 0);
                            crate::leanh::lean_dec(v_unused_2427_);
                            v___x_2391_ = v_x_2377_;
                            v_isShared_2392_ = v_isSharedCheck_2426_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2377_);
                            v___x_2391_ = crate::leanh::lean_box(0);
                            v_isShared_2392_ = v_isSharedCheck_2426_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2428_ = crate::leanh::lean_ctor_get(v_x_2377_, 0);
                    v_vs_2429_ = crate::leanh::lean_ctor_get(v_x_2377_, 1);
                    v_isSharedCheck_2449_ = (!crate::leanh::lean_is_exclusive(v_x_2377_)) as u8;
                    if v_isSharedCheck_2449_ == 0 {
                        v___x_2431_ = v_x_2377_;
                        v_isShared_2432_ = v_isSharedCheck_2449_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2429_);
                        crate::leanh::lean_inc(v_ks_2428_);
                        crate::leanh::lean_dec(v_x_2377_);
                        v___x_2431_ = crate::leanh::lean_box(0);
                        v_isShared_2432_ = v_isSharedCheck_2449_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2393_ = lean_array_fget(v_es_2382_, v_j_2387_);
                v___x_2394_ = crate::leanh::lean_box(0);
                v_xs_x27_2395_ = lean_array_fset(v_es_2382_, v_j_2387_, v___x_2394_);
                match crate::leanh::lean_obj_tag(v_v_2393_) {
                    0 => {
                        v_key_2402_ = crate::leanh::lean_ctor_get(v_v_2393_, 0);
                        v_val_2403_ = crate::leanh::lean_ctor_get(v_v_2393_, 1);
                        v_isSharedCheck_2413_ = (!crate::leanh::lean_is_exclusive(v_v_2393_)) as u8;
                        if v_isSharedCheck_2413_ == 0 {
                            v___x_2405_ = v_v_2393_;
                            v_isShared_2406_ = v_isSharedCheck_2413_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2403_);
                            crate::leanh::lean_inc(v_key_2402_);
                            crate::leanh::lean_dec(v_v_2393_);
                            v___x_2405_ = crate::leanh::lean_box(0);
                            v_isShared_2406_ = v_isSharedCheck_2413_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2414_ = crate::leanh::lean_ctor_get(v_v_2393_, 0);
                        v_isSharedCheck_2424_ = (!crate::leanh::lean_is_exclusive(v_v_2393_)) as u8;
                        if v_isSharedCheck_2424_ == 0 {
                            v___x_2416_ = v_v_2393_;
                            v_isShared_2417_ = v_isSharedCheck_2424_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2414_);
                            crate::leanh::lean_dec(v_v_2393_);
                            v___x_2416_ = crate::leanh::lean_box(0);
                            v_isShared_2417_ = v_isSharedCheck_2424_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2425_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2425_, 0, v_x_2380_);
                        crate::leanh::lean_ctor_set(v___x_2425_, 1, v_x_2381_);
                        v___y_2397_ = v___x_2425_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2398_ = lean_array_fset(v_xs_x27_2395_, v_j_2387_, v___y_2397_);
                crate::leanh::lean_dec(v_j_2387_);
                if v_isShared_2392_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2391_, 0, v___x_2398_);
                    v___x_2400_ = v___x_2391_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
                    v___x_2400_ = v_reuseFailAlloc_2401_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2400_;
            }
            4 => {
                v___x_2407_ = lean_string_dec_eq(v_x_2380_, v_key_2402_);
                if v___x_2407_ == 0 {
                    crate::leanh::lean_del_object(v___x_2405_);
                    v___x_2408_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2402_,
                        v_val_2403_,
                        v_x_2380_,
                        v_x_2381_,
                    );
                    v___x_2409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2409_, 0, v___x_2408_);
                    v___y_2397_ = v___x_2409_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2403_);
                    crate::leanh::lean_dec(v_key_2402_);
                    if v_isShared_2406_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2405_, 1, v_x_2381_);
                        crate::leanh::lean_ctor_set(v___x_2405_, 0, v_x_2380_);
                        v___x_2411_ = v___x_2405_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2412_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_x_2380_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_x_2381_);
                        v___x_2411_ = v_reuseFailAlloc_2412_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2397_ = v___x_2411_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2418_ = lean_usize_shift_right(v_x_2378_, v___x_2383_);
                v___x_2419_ = lean_usize_add(v_x_2379_, v___x_2384_);
                v___x_2420_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_node_2414_, v___x_2418_, v___x_2419_, v_x_2380_, v_x_2381_);
                if v_isShared_2417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2416_, 0, v___x_2420_);
                    v___x_2422_ = v___x_2416_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
                    v___x_2422_ = v_reuseFailAlloc_2423_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2397_ = v___x_2422_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2432_ == 0 {
                    v___x_2434_ = v___x_2431_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2448_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_ks_2428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_vs_2429_);
                    v___x_2434_ = v_reuseFailAlloc_2448_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2435_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v___x_2434_, v_x_2380_, v_x_2381_);
                v___x_2443_ = 7usize;
                v___x_2444_ = lean_usize_dec_le(v___x_2443_, v_x_2379_);
                if v___x_2444_ == 0 {
                    v___x_2445_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2435_);
                    v___x_2446_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2447_ = lean_nat_dec_lt(v___x_2445_, v___x_2446_);
                    crate::leanh::lean_dec(v___x_2445_);
                    v___y_2437_ = v___x_2447_;
                    state = 10;
                    continue;
                } else {
                    v___y_2437_ = v___x_2444_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2437_ == 0 {
                    v_ks_2438_ = crate::leanh::lean_ctor_get(v_newNode_2435_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2438_);
                    v_vs_2439_ = crate::leanh::lean_ctor_get(v_newNode_2435_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2439_);
                    crate::leanh::lean_dec_ref(v_newNode_2435_);
                    v___x_2440_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2441_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___closed__0);
                    v___x_2442_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_x_2379_, v_ks_2438_, v_vs_2439_, v___x_2440_, v___x_2441_);
                    crate::leanh::lean_dec_ref(v_vs_2439_);
                    crate::leanh::lean_dec_ref(v_ks_2438_);
                    return v___x_2442_;
                } else {
                    return v_newNode_2435_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(
    mut v_depth_2450_: usize,
    mut v_keys_2451_: *mut crate::leanh::LeanObject,
    mut v_vals_2452_: *mut crate::leanh::LeanObject,
    mut v_i_2453_: *mut crate::leanh::LeanObject,
    mut v_entries_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: u8 = 0;
    let mut v_k_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: u64 = 0;
    let mut v_h_2460_: usize = 0;
    let mut v___x_2461_: usize = 0;
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: usize = 0;
    let mut v___x_2464_: usize = 0;
    let mut v___x_2465_: usize = 0;
    let mut v_h_2466_: usize = 0;
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2455_ = lean_array_get_size(v_keys_2451_);
                v___x_2456_ = lean_nat_dec_lt(v_i_2453_, v___x_2455_);
                if v___x_2456_ == 0 {
                    crate::leanh::lean_dec(v_i_2453_);
                    return v_entries_2454_;
                } else {
                    v_k_2457_ = lean_array_fget_borrowed(v_keys_2451_, v_i_2453_);
                    v_v_2458_ = lean_array_fget_borrowed(v_vals_2452_, v_i_2453_);
                    v___x_2459_ = lean_string_hash(v_k_2457_);
                    v_h_2460_ = lean_uint64_to_usize(v___x_2459_);
                    v___x_2461_ = 5usize;
                    v___x_2462_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2463_ = 1usize;
                    v___x_2464_ = lean_usize_sub(v_depth_2450_, v___x_2463_);
                    v___x_2465_ = lean_usize_mul(v___x_2461_, v___x_2464_);
                    v_h_2466_ = lean_usize_shift_right(v_h_2460_, v___x_2465_);
                    v___x_2467_ = lean_nat_add(v_i_2453_, v___x_2462_);
                    crate::leanh::lean_dec(v_i_2453_);
                    crate::leanh::lean_inc(v_v_2458_);
                    crate::leanh::lean_inc(v_k_2457_);
                    v___x_2468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_entries_2454_, v_h_2466_, v_depth_2450_, v_k_2457_, v_v_2458_);
                    v_i_2453_ = v___x_2467_;
                    v_entries_2454_ = v___x_2468_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg___boxed(
    mut v_depth_2470_: *mut crate::leanh::LeanObject,
    mut v_keys_2471_: *mut crate::leanh::LeanObject,
    mut v_vals_2472_: *mut crate::leanh::LeanObject,
    mut v_i_2473_: *mut crate::leanh::LeanObject,
    mut v_entries_2474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2475_: usize = 0;
    let mut v_res_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2475_ = crate::leanh::lean_unbox_usize(v_depth_2470_);
    crate::leanh::lean_dec(v_depth_2470_);
    v_res_2476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_boxed_2475_, v_keys_2471_, v_vals_2472_, v_i_2473_, v_entries_2474_);
    crate::leanh::lean_dec_ref(v_vals_2472_);
    crate::leanh::lean_dec_ref(v_keys_2471_);
    return v_res_2476_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg___boxed(
    mut v_x_2477_: *mut crate::leanh::LeanObject,
    mut v_x_2478_: *mut crate::leanh::LeanObject,
    mut v_x_2479_: *mut crate::leanh::LeanObject,
    mut v_x_2480_: *mut crate::leanh::LeanObject,
    mut v_x_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_817__boxed_2482_: usize = 0;
    let mut v_x_818__boxed_2483_: usize = 0;
    let mut v_res_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_817__boxed_2482_ = crate::leanh::lean_unbox_usize(v_x_2478_);
    crate::leanh::lean_dec(v_x_2478_);
    v_x_818__boxed_2483_ = crate::leanh::lean_unbox_usize(v_x_2479_);
    crate::leanh::lean_dec(v_x_2479_);
    v_res_2484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_2477_, v_x_817__boxed_2482_, v_x_818__boxed_2483_, v_x_2480_, v_x_2481_);
    return v_res_2484_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(
    mut v_x_2485_: *mut crate::leanh::LeanObject,
    mut v_x_2486_: *mut crate::leanh::LeanObject,
    mut v_x_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2488_: u64 = 0;
    let mut v___x_2489_: usize = 0;
    let mut v___x_2490_: usize = 0;
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2488_ = lean_string_hash(v_x_2486_);
    v___x_2489_ = lean_uint64_to_usize(v___x_2488_);
    v___x_2490_ = 1usize;
    v___x_2491_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_2485_, v___x_2489_, v___x_2490_, v_x_2486_, v_x_2487_);
    return v___x_2491_;
}
pub unsafe fn l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(
    mut v_params_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2500_: u8 = 0;
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2511_: u8 = 0;
    let mut v_a_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_params_2494_);
                v___x_2495_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(v_params_2494_);
                if crate::leanh::lean_obj_tag(v___x_2495_) == 0 {
                    v_a_2496_ = crate::leanh::lean_ctor_get(v___x_2495_, 0);
                    v_isSharedCheck_2511_ = (!crate::leanh::lean_is_exclusive(v___x_2495_)) as u8;
                    if v_isSharedCheck_2511_ == 0 {
                        v___x_2498_ = v___x_2495_;
                        v_isShared_2499_ = v_isSharedCheck_2511_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2496_);
                        crate::leanh::lean_dec(v___x_2495_);
                        v___x_2498_ = crate::leanh::lean_box(0);
                        v_isShared_2499_ = v_isSharedCheck_2511_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_params_2494_);
                    v_a_2512_ = crate::leanh::lean_ctor_get(v___x_2495_, 0);
                    v_isSharedCheck_2519_ = (!crate::leanh::lean_is_exclusive(v___x_2495_)) as u8;
                    if v_isSharedCheck_2519_ == 0 {
                        v___x_2514_ = v___x_2495_;
                        v_isShared_2515_ = v_isSharedCheck_2519_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2512_);
                        crate::leanh::lean_dec(v___x_2495_);
                        v___x_2514_ = crate::leanh::lean_box(0);
                        v_isShared_2515_ = v_isSharedCheck_2519_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2500_ = 3;
                v___x_2501_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__0;
                v___x_2502_ = l_Lean_Json_compress(v_params_2494_);
                v___x_2503_ = lean_string_append(v___x_2501_, v___x_2502_);
                crate::leanh::lean_dec_ref(v___x_2502_);
                v___x_2504_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0___closed__1;
                v___x_2505_ = lean_string_append(v___x_2503_, v___x_2504_);
                v___x_2506_ = lean_string_append(v___x_2505_, v_a_2496_);
                crate::leanh::lean_dec(v_a_2496_);
                v___x_2507_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2507_, 0, v___x_2506_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2507_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2500_,
                );
                if v_isShared_2499_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2498_, 0, v___x_2507_);
                    v___x_2509_ = v___x_2498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
                    v___x_2509_ = v_reuseFailAlloc_2510_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2509_;
            }
            3 => {
                if v_isShared_2515_ == 0 {
                    v___x_2517_ = v___x_2514_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
                    v___x_2517_ = v_reuseFailAlloc_2518_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_params_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2530_: u8 = 0;
    let mut v_a_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2522_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_params_2520_);
                if crate::leanh::lean_obj_tag(v___x_2522_) == 0 {
                    v_a_2523_ = crate::leanh::lean_ctor_get(v___x_2522_, 0);
                    v_isSharedCheck_2530_ = (!crate::leanh::lean_is_exclusive(v___x_2522_)) as u8;
                    if v_isSharedCheck_2530_ == 0 {
                        v___x_2525_ = v___x_2522_;
                        v_isShared_2526_ = v_isSharedCheck_2530_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2523_);
                        crate::leanh::lean_dec(v___x_2522_);
                        v___x_2525_ = crate::leanh::lean_box(0);
                        v_isShared_2526_ = v_isSharedCheck_2530_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2531_ = crate::leanh::lean_ctor_get(v___x_2522_, 0);
                    v_isSharedCheck_2538_ = (!crate::leanh::lean_is_exclusive(v___x_2522_)) as u8;
                    if v_isSharedCheck_2538_ == 0 {
                        v___x_2533_ = v___x_2522_;
                        v_isShared_2534_ = v_isSharedCheck_2538_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2531_);
                        crate::leanh::lean_dec(v___x_2522_);
                        v___x_2533_ = crate::leanh::lean_box(0);
                        v_isShared_2534_ = v_isSharedCheck_2538_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2526_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2525_, 1);
                    v___x_2528_ = v___x_2525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
                    v___x_2528_ = v_reuseFailAlloc_2529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2528_;
            }
            3 => {
                if v_isShared_2534_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2533_, 0);
                    v___x_2536_ = v___x_2533_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2537_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
                    v___x_2536_ = v_reuseFailAlloc_2537_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(
    mut v_params_2539_: *mut crate::leanh::LeanObject,
    mut v_a_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2541_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2539_);
    return v_res_2541_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(
    mut v_handler_2542_: *mut crate::leanh::LeanObject,
    mut v___f_2543_: *mut crate::leanh::LeanObject,
    mut v_j_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v_a_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut v_a_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2570_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2547_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_j_2544_);
                if crate::leanh::lean_obj_tag(v___x_2547_) == 0 {
                    v_a_2548_ = crate::leanh::lean_ctor_get(v___x_2547_, 0);
                    crate::leanh::lean_inc(v_a_2548_);
                    crate::leanh::lean_dec_ref_known(v___x_2547_, 1);
                    crate::leanh::lean_inc_ref(v___y_2545_);
                    v___x_2549_ = crate::leanh::lean_apply_3(
                        v_handler_2542_,
                        v_a_2548_,
                        v___y_2545_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2549_) == 0 {
                        v_a_2550_ = crate::leanh::lean_ctor_get(v___x_2549_, 0);
                        v_isSharedCheck_2558_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2549_)) as u8;
                        if v_isSharedCheck_2558_ == 0 {
                            v___x_2552_ = v___x_2549_;
                            v_isShared_2553_ = v_isSharedCheck_2558_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2550_);
                            crate::leanh::lean_dec(v___x_2549_);
                            v___x_2552_ = crate::leanh::lean_box(0);
                            v_isShared_2553_ = v_isSharedCheck_2558_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_2543_);
                        v_a_2559_ = crate::leanh::lean_ctor_get(v___x_2549_, 0);
                        v_isSharedCheck_2566_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2549_)) as u8;
                        if v_isSharedCheck_2566_ == 0 {
                            v___x_2561_ = v___x_2549_;
                            v_isShared_2562_ = v_isSharedCheck_2566_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2559_);
                            crate::leanh::lean_dec(v___x_2549_);
                            v___x_2561_ = crate::leanh::lean_box(0);
                            v_isShared_2562_ = v_isSharedCheck_2566_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2543_);
                    crate::leanh::lean_dec_ref(v_handler_2542_);
                    v_a_2567_ = crate::leanh::lean_ctor_get(v___x_2547_, 0);
                    v_isSharedCheck_2574_ = (!crate::leanh::lean_is_exclusive(v___x_2547_)) as u8;
                    if v_isSharedCheck_2574_ == 0 {
                        v___x_2569_ = v___x_2547_;
                        v_isShared_2570_ = v_isSharedCheck_2574_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2567_);
                        crate::leanh::lean_dec(v___x_2547_);
                        v___x_2569_ = crate::leanh::lean_box(0);
                        v_isShared_2570_ = v_isSharedCheck_2574_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2554_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2543_, v_a_2550_);
                if v_isShared_2553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2554_);
                    v___x_2556_ = v___x_2552_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2557_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
                    v___x_2556_ = v_reuseFailAlloc_2557_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2556_;
            }
            3 => {
                if v_isShared_2562_ == 0 {
                    v___x_2564_ = v___x_2561_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
                    v___x_2564_ = v_reuseFailAlloc_2565_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2564_;
            }
            5 => {
                if v_isShared_2570_ == 0 {
                    v___x_2572_ = v___x_2569_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2573_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
                    v___x_2572_ = v_reuseFailAlloc_2573_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed(
    mut v_handler_2575_: *mut crate::leanh::LeanObject,
    mut v___f_2576_: *mut crate::leanh::LeanObject,
    mut v_j_2577_: *mut crate::leanh::LeanObject,
    mut v___y_2578_: *mut crate::leanh::LeanObject,
    mut v___y_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2580_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2(v_handler_2575_, v___f_2576_, v_j_2577_, v___y_2578_);
    crate::leanh::lean_dec_ref(v___y_2578_);
    return v_res_2580_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__0(
    mut v_j_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2586_: u8 = 0;
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut v_a_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2594_: u8 = 0;
    let mut v_toTextDocumentPositionParams_2595_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_textDocument_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2582_ = l_Lean_Server_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__0(v_j_2581_);
                if crate::leanh::lean_obj_tag(v___x_2582_) == 0 {
                    v_a_2583_ = crate::leanh::lean_ctor_get(v___x_2582_, 0);
                    v_isSharedCheck_2590_ = (!crate::leanh::lean_is_exclusive(v___x_2582_)) as u8;
                    if v_isSharedCheck_2590_ == 0 {
                        v___x_2585_ = v___x_2582_;
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2583_);
                        crate::leanh::lean_dec(v___x_2582_);
                        v___x_2585_ = crate::leanh::lean_box(0);
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2591_ = crate::leanh::lean_ctor_get(v___x_2582_, 0);
                    v_isSharedCheck_2600_ = (!crate::leanh::lean_is_exclusive(v___x_2582_)) as u8;
                    if v_isSharedCheck_2600_ == 0 {
                        v___x_2593_ = v___x_2582_;
                        v_isShared_2594_ = v_isSharedCheck_2600_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2591_);
                        crate::leanh::lean_dec(v___x_2582_);
                        v___x_2593_ = crate::leanh::lean_box(0);
                        v_isShared_2594_ = v_isSharedCheck_2600_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2586_ == 0 {
                    v___x_2588_ = v___x_2585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
                    v___x_2588_ = v_reuseFailAlloc_2589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2588_;
            }
            3 => {
                v_toTextDocumentPositionParams_2595_ = crate::leanh::lean_ctor_get(v_a_2591_, 0);
                crate::leanh::lean_inc_ref(v_toTextDocumentPositionParams_2595_);
                crate::leanh::lean_dec(v_a_2591_);
                v_textDocument_2596_ =
                    crate::leanh::lean_ctor_get(v_toTextDocumentPositionParams_2595_, 0);
                crate::leanh::lean_inc_ref(v_textDocument_2596_);
                crate::leanh::lean_dec_ref(v_toTextDocumentPositionParams_2595_);
                if v_isShared_2594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2593_, 0, v_textDocument_2596_);
                    v___x_2598_ = v___x_2593_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_textDocument_2596_);
                    v___x_2598_ = v_reuseFailAlloc_2599_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_keys_2601_: *mut crate::leanh::LeanObject,
    mut v_i_2602_: *mut crate::leanh::LeanObject,
    mut v_k_2603_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: u8 = 0;
    let mut v_k_x27_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2604_ = lean_array_get_size(v_keys_2601_);
                v___x_2605_ = lean_nat_dec_lt(v_i_2602_, v___x_2604_);
                if v___x_2605_ == 0 {
                    crate::leanh::lean_dec(v_i_2602_);
                    return v___x_2605_;
                } else {
                    v_k_x27_2606_ = lean_array_fget_borrowed(v_keys_2601_, v_i_2602_);
                    v___x_2607_ = lean_string_dec_eq(v_k_2603_, v_k_x27_2606_);
                    if v___x_2607_ == 0 {
                        v___x_2608_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2609_ = lean_nat_add(v_i_2602_, v___x_2608_);
                        crate::leanh::lean_dec(v_i_2602_);
                        v_i_2602_ = v___x_2609_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_2602_);
                        return v___x_2607_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_keys_2611_: *mut crate::leanh::LeanObject,
    mut v_i_2612_: *mut crate::leanh::LeanObject,
    mut v_k_2613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2614_: u8 = 0;
    let mut v_r_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2614_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_2611_, v_i_2612_, v_k_2613_);
    crate::leanh::lean_dec_ref(v_k_2613_);
    crate::leanh::lean_dec_ref(v_keys_2611_);
    v_r_2615_ = crate::leanh::lean_box((v_res_2614_) as usize);
    return v_r_2615_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(
    mut v_x_2616_: *mut crate::leanh::LeanObject,
    mut v_x_2617_: usize,
    mut v_x_2618_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: usize = 0;
    let mut v___x_2622_: usize = 0;
    let mut v___x_2623_: usize = 0;
    let mut v_j_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: u8 = 0;
    let mut v_node_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: usize = 0;
    let mut v___x_2631_: u8 = 0;
    let mut v_ks_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2616_) == 0 {
                    v_es_2619_ = crate::leanh::lean_ctor_get(v_x_2616_, 0);
                    v___x_2620_ = crate::leanh::lean_box(2);
                    v___x_2621_ = 5usize;
                    v___x_2622_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0_spec__0___redArg___closed__1);
                    v___x_2623_ = lean_usize_land(v_x_2617_, v___x_2622_);
                    v_j_2624_ = lean_usize_to_nat(v___x_2623_);
                    v___x_2625_ = lean_array_get_borrowed(v___x_2620_, v_es_2619_, v_j_2624_);
                    crate::leanh::lean_dec(v_j_2624_);
                    match crate::leanh::lean_obj_tag(v___x_2625_) {
                        0 => {
                            v_key_2626_ = crate::leanh::lean_ctor_get(v___x_2625_, 0);
                            v___x_2627_ = lean_string_dec_eq(v_x_2618_, v_key_2626_);
                            return v___x_2627_;
                        }
                        1 => {
                            v_node_2628_ = crate::leanh::lean_ctor_get(v___x_2625_, 0);
                            v___x_2629_ = lean_usize_shift_right(v_x_2617_, v___x_2621_);
                            v_x_2616_ = v_node_2628_;
                            v_x_2617_ = v___x_2629_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2631_ = 0;
                            return v___x_2631_;
                        }
                    }
                } else {
                    v_ks_2632_ = crate::leanh::lean_ctor_get(v_x_2616_, 0);
                    v___x_2633_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2634_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_ks_2632_, v___x_2633_, v_x_2618_);
                    return v___x_2634_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg___boxed(
    mut v_x_2635_: *mut crate::leanh::LeanObject,
    mut v_x_2636_: *mut crate::leanh::LeanObject,
    mut v_x_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1197__boxed_2638_: usize = 0;
    let mut v_res_2639_: u8 = 0;
    let mut v_r_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1197__boxed_2638_ = crate::leanh::lean_unbox_usize(v_x_2636_);
    crate::leanh::lean_dec(v_x_2636_);
    v_res_2639_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_2635_, v_x_1197__boxed_2638_, v_x_2637_);
    crate::leanh::lean_dec_ref(v_x_2637_);
    crate::leanh::lean_dec_ref(v_x_2635_);
    v_r_2640_ = crate::leanh::lean_box((v_res_2639_) as usize);
    return v_r_2640_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(
    mut v_x_2641_: *mut crate::leanh::LeanObject,
    mut v_x_2642_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2643_: u64 = 0;
    let mut v___x_2644_: usize = 0;
    let mut v___x_2645_: u8 = 0;
    v___x_2643_ = lean_string_hash(v_x_2642_);
    v___x_2644_ = lean_uint64_to_usize(v___x_2643_);
    v___x_2645_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_2641_, v___x_2644_, v_x_2642_);
    return v___x_2645_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg___boxed(
    mut v_x_2646_: *mut crate::leanh::LeanObject,
    mut v_x_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2648_: u8 = 0;
    let mut v_r_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2648_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_2646_, v_x_2647_);
    crate::leanh::lean_dec_ref(v_x_2647_);
    crate::leanh::lean_dec_ref(v_x_2646_);
    v_r_2649_ = crate::leanh::lean_box((v_res_2648_) as usize);
    return v_r_2649_;
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(
    mut v_method_2654_: *mut crate::leanh::LeanObject,
    mut v_handler_2655_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: u8 = 0;
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_a_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2658_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_2658_) == 0 {
                    v_a_2659_ = crate::leanh::lean_ctor_get(v___x_2658_, 0);
                    v_isSharedCheck_2693_ = (!crate::leanh::lean_is_exclusive(v___x_2658_)) as u8;
                    if v_isSharedCheck_2693_ == 0 {
                        v___x_2661_ = v___x_2658_;
                        v_isShared_2662_ = v_isSharedCheck_2693_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2659_);
                        crate::leanh::lean_dec(v___x_2658_);
                        v___x_2661_ = crate::leanh::lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2693_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_serialize_x3f_2656_);
                    crate::leanh::lean_dec_ref(v_handler_2655_);
                    crate::leanh::lean_dec_ref(v_method_2654_);
                    v_a_2694_ = crate::leanh::lean_ctor_get(v___x_2658_, 0);
                    v_isSharedCheck_2701_ = (!crate::leanh::lean_is_exclusive(v___x_2658_)) as u8;
                    if v_isSharedCheck_2701_ == 0 {
                        v___x_2696_ = v___x_2658_;
                        v_isShared_2697_ = v_isSharedCheck_2701_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2694_);
                        crate::leanh::lean_dec(v___x_2658_);
                        v___x_2696_ = crate::leanh::lean_box(0);
                        v_isShared_2697_ = v_isSharedCheck_2701_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2663_ = (crate::leanh::lean_unbox(v_a_2659_) as u8);
                if v___x_2663_ == 0 {
                    crate::leanh::lean_dec(v_a_2659_);
                    crate::leanh::lean_dec(v_serialize_x3f_2656_);
                    crate::leanh::lean_dec_ref(v_handler_2655_);
                    v___x_2664_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0;
                    v___x_2665_ = lean_string_append(v___x_2664_, v_method_2654_);
                    crate::leanh::lean_dec_ref(v_method_2654_);
                    v___x_2666_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__1;
                    v___x_2667_ = lean_string_append(v___x_2665_, v___x_2666_);
                    v___x_2668_ = lean_mk_io_user_error(v___x_2667_);
                    if v_isShared_2662_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2661_, 1);
                        crate::leanh::lean_ctor_set(v___x_2661_, 0, v___x_2668_);
                        v___x_2670_ = v___x_2661_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
                        v___x_2670_ = v_reuseFailAlloc_2671_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2672_ = l_Lean_Server_requestHandlers;
                    v___x_2673_ = lean_st_ref_get(v___x_2672_);
                    v___x_2674_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v___x_2673_, v_method_2654_);
                    crate::leanh::lean_dec(v___x_2673_);
                    if v___x_2674_ == 0 {
                        v___x_2675_ = lean_st_ref_take(v___x_2672_);
                        v___f_2676_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__2;
                        v___f_2677_ = crate::leanh::lean_alloc_closure(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_2677_, 0, v_serialize_x3f_2656_);
                        crate::leanh::lean_closure_set(v___f_2677_, 1, v_a_2659_);
                        v___f_2678_ = crate::leanh::lean_alloc_closure(l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___lam__2___boxed as *mut core::ffi::c_void, 5, 2);
                        crate::leanh::lean_closure_set(v___f_2678_, 0, v_handler_2655_);
                        crate::leanh::lean_closure_set(v___f_2678_, 1, v___f_2677_);
                        v___x_2679_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2679_, 0, v___f_2676_);
                        crate::leanh::lean_ctor_set(v___x_2679_, 1, v___f_2678_);
                        v___x_2680_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v___x_2675_, v_method_2654_, v___x_2679_);
                        v___x_2681_ = lean_st_ref_set(v___x_2672_, v___x_2680_);
                        if v_isShared_2662_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2661_, 0, v___x_2681_);
                            v___x_2683_ = v___x_2661_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2684_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
                            v___x_2683_ = v_reuseFailAlloc_2684_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2659_);
                        crate::leanh::lean_dec(v_serialize_x3f_2656_);
                        crate::leanh::lean_dec_ref(v_handler_2655_);
                        v___x_2685_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__0;
                        v___x_2686_ = lean_string_append(v___x_2685_, v_method_2654_);
                        crate::leanh::lean_dec_ref(v_method_2654_);
                        v___x_2687_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___closed__3;
                        v___x_2688_ = lean_string_append(v___x_2686_, v___x_2687_);
                        v___x_2689_ = lean_mk_io_user_error(v___x_2688_);
                        if v_isShared_2662_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2661_, 1);
                            crate::leanh::lean_ctor_set(v___x_2661_, 0, v___x_2689_);
                            v___x_2691_ = v___x_2661_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2692_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
                            v___x_2691_ = v_reuseFailAlloc_2692_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2670_;
            }
            3 => {
                return v___x_2683_;
            }
            4 => {
                return v___x_2691_;
            }
            5 => {
                if v_isShared_2697_ == 0 {
                    v___x_2699_ = v___x_2696_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
                    v___x_2699_ = v_reuseFailAlloc_2700_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0___boxed(
    mut v_method_2702_: *mut crate::leanh::LeanObject,
    mut v_handler_2703_: *mut crate::leanh::LeanObject,
    mut v_serialize_x3f_2704_: *mut crate::leanh::LeanObject,
    mut v_a_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2706_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v_method_2702_, v_handler_2703_, v_serialize_x3f_2704_);
    return v_res_2706_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2710_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_;
    v___x_2711_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_;
    v___x_2712_ = crate::leanh::lean_box(0);
    v___x_2713_ = l_Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0(v___x_2710_, v___x_2711_, v___x_2712_);
    return v___x_2713_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2____boxed(
    mut v_a_2714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2715_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
    return v_res_2715_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(
    mut v_params_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2719_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___redArg(v_params_2716_);
    return v___x_2719_;
}
pub unsafe fn l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_params_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2723_ = l_Lean_Server_RequestM_parseRequestParams___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__1(v_params_2720_, v_a_2721_);
    crate::leanh::lean_dec_ref(v_a_2721_);
    return v_res_2723_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(
    mut v_00_u03b2_2724_: *mut crate::leanh::LeanObject,
    mut v_x_2725_: *mut crate::leanh::LeanObject,
    mut v_x_2726_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2727_: u8 = 0;
    v___x_2727_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___redArg(v_x_2725_, v_x_2726_);
    return v___x_2727_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2___boxed(
    mut v_00_u03b2_2728_: *mut crate::leanh::LeanObject,
    mut v_x_2729_: *mut crate::leanh::LeanObject,
    mut v_x_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2731_: u8 = 0;
    let mut v_r_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2731_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2(v_00_u03b2_2728_, v_x_2729_, v_x_2730_);
    crate::leanh::lean_dec_ref(v_x_2730_);
    crate::leanh::lean_dec_ref(v_x_2729_);
    v_r_2732_ = crate::leanh::lean_box((v_res_2731_) as usize);
    return v_r_2732_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3(
    mut v_00_u03b2_2733_: *mut crate::leanh::LeanObject,
    mut v_x_2734_: *mut crate::leanh::LeanObject,
    mut v_x_2735_: *mut crate::leanh::LeanObject,
    mut v_x_2736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2737_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3___redArg(v_x_2734_, v_x_2735_, v_x_2736_);
    return v___x_2737_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(
    mut v_00_u03b2_2738_: *mut crate::leanh::LeanObject,
    mut v_x_2739_: *mut crate::leanh::LeanObject,
    mut v_x_2740_: usize,
    mut v_x_2741_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2742_: u8 = 0;
    v___x_2742_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___redArg(v_x_2739_, v_x_2740_, v_x_2741_);
    return v___x_2742_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3___boxed(
    mut v_00_u03b2_2743_: *mut crate::leanh::LeanObject,
    mut v_x_2744_: *mut crate::leanh::LeanObject,
    mut v_x_2745_: *mut crate::leanh::LeanObject,
    mut v_x_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1394__boxed_2747_: usize = 0;
    let mut v_res_2748_: u8 = 0;
    let mut v_r_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1394__boxed_2747_ = crate::leanh::lean_unbox_usize(v_x_2745_);
    crate::leanh::lean_dec(v_x_2745_);
    v_res_2748_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3(v_00_u03b2_2743_, v_x_2744_, v_x_1394__boxed_2747_, v_x_2746_);
    crate::leanh::lean_dec_ref(v_x_2746_);
    crate::leanh::lean_dec_ref(v_x_2744_);
    v_r_2749_ = crate::leanh::lean_box((v_res_2748_) as usize);
    return v_r_2749_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(
    mut v_00_u03b2_2750_: *mut crate::leanh::LeanObject,
    mut v_x_2751_: *mut crate::leanh::LeanObject,
    mut v_x_2752_: usize,
    mut v_x_2753_: usize,
    mut v_x_2754_: *mut crate::leanh::LeanObject,
    mut v_x_2755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___redArg(v_x_2751_, v_x_2752_, v_x_2753_, v_x_2754_, v_x_2755_);
    return v___x_2756_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5___boxed(
    mut v_00_u03b2_2757_: *mut crate::leanh::LeanObject,
    mut v_x_2758_: *mut crate::leanh::LeanObject,
    mut v_x_2759_: *mut crate::leanh::LeanObject,
    mut v_x_2760_: *mut crate::leanh::LeanObject,
    mut v_x_2761_: *mut crate::leanh::LeanObject,
    mut v_x_2762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1405__boxed_2763_: usize = 0;
    let mut v_x_1406__boxed_2764_: usize = 0;
    let mut v_res_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1405__boxed_2763_ = crate::leanh::lean_unbox_usize(v_x_2759_);
    crate::leanh::lean_dec(v_x_2759_);
    v_x_1406__boxed_2764_ = crate::leanh::lean_unbox_usize(v_x_2760_);
    crate::leanh::lean_dec(v_x_2760_);
    v_res_2765_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5(v_00_u03b2_2757_, v_x_2758_, v_x_1405__boxed_2763_, v_x_1406__boxed_2764_, v_x_2761_, v_x_2762_);
    return v_res_2765_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2766_: *mut crate::leanh::LeanObject,
    mut v_keys_2767_: *mut crate::leanh::LeanObject,
    mut v_vals_2768_: *mut crate::leanh::LeanObject,
    mut v_heq_2769_: *mut crate::leanh::LeanObject,
    mut v_i_2770_: *mut crate::leanh::LeanObject,
    mut v_k_2771_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2772_: u8 = 0;
    v___x_2772_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___redArg(v_keys_2767_, v_i_2770_, v_k_2771_);
    return v___x_2772_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_2773_: *mut crate::leanh::LeanObject,
    mut v_keys_2774_: *mut crate::leanh::LeanObject,
    mut v_vals_2775_: *mut crate::leanh::LeanObject,
    mut v_heq_2776_: *mut crate::leanh::LeanObject,
    mut v_i_2777_: *mut crate::leanh::LeanObject,
    mut v_k_2778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2779_: u8 = 0;
    let mut v_r_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2779_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__2_spec__3_spec__4(v_00_u03b2_2773_, v_keys_2774_, v_vals_2775_, v_heq_2776_, v_i_2777_, v_k_2778_);
    crate::leanh::lean_dec_ref(v_k_2778_);
    crate::leanh::lean_dec_ref(v_vals_2775_);
    crate::leanh::lean_dec_ref(v_keys_2774_);
    v_r_2780_ = crate::leanh::lean_box((v_res_2779_) as usize);
    return v_r_2780_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7(
    mut v_00_u03b2_2781_: *mut crate::leanh::LeanObject,
    mut v_n_2782_: *mut crate::leanh::LeanObject,
    mut v_k_2783_: *mut crate::leanh::LeanObject,
    mut v_v_2784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2785_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7___redArg(v_n_2782_, v_k_2783_, v_v_2784_);
    return v___x_2785_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(
    mut v_00_u03b2_2786_: *mut crate::leanh::LeanObject,
    mut v_depth_2787_: usize,
    mut v_keys_2788_: *mut crate::leanh::LeanObject,
    mut v_vals_2789_: *mut crate::leanh::LeanObject,
    mut v_heq_2790_: *mut crate::leanh::LeanObject,
    mut v_i_2791_: *mut crate::leanh::LeanObject,
    mut v_entries_2792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2793_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___redArg(v_depth_2787_, v_keys_2788_, v_vals_2789_, v_i_2791_, v_entries_2792_);
    return v___x_2793_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8___boxed(
    mut v_00_u03b2_2794_: *mut crate::leanh::LeanObject,
    mut v_depth_2795_: *mut crate::leanh::LeanObject,
    mut v_keys_2796_: *mut crate::leanh::LeanObject,
    mut v_vals_2797_: *mut crate::leanh::LeanObject,
    mut v_heq_2798_: *mut crate::leanh::LeanObject,
    mut v_i_2799_: *mut crate::leanh::LeanObject,
    mut v_entries_2800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2801_: usize = 0;
    let mut v_res_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2801_ = crate::leanh::lean_unbox_usize(v_depth_2795_);
    crate::leanh::lean_dec(v_depth_2795_);
    v_res_2802_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__8(v_00_u03b2_2794_, v_depth_boxed_2801_, v_keys_2796_, v_vals_2797_, v_heq_2798_, v_i_2799_, v_entries_2800_);
    crate::leanh::lean_dec_ref(v_vals_2797_);
    crate::leanh::lean_dec_ref(v_keys_2796_);
    return v_res_2802_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8(
    mut v_00_u03b2_2803_: *mut crate::leanh::LeanObject,
    mut v_x_2804_: *mut crate::leanh::LeanObject,
    mut v_x_2805_: *mut crate::leanh::LeanObject,
    mut v_x_2806_: *mut crate::leanh::LeanObject,
    mut v_x_2807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2808_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_registerLspRequestHandler___at___00__private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2__spec__0_spec__3_spec__5_spec__7_spec__8___redArg(v_x_2804_, v_x_2805_, v_x_2806_, v_x_2807_);
    return v___x_2808_;
}
pub unsafe fn l_Lean_Server_wrapRpcProcedure___redArg___lam__0(
    mut v_x_2809_: u64,
    mut v_y_2810_: u64,
) -> u8 {
    let mut v___x_2811_: u8 = 0;
    v___x_2811_ = lean_uint64_dec_lt(v_x_2809_, v_y_2810_);
    if v___x_2811_ == 0 {
        let mut v___x_2812_: u8 = 0;
        v___x_2812_ = lean_uint64_dec_eq(v_x_2809_, v_y_2810_);
        if v___x_2812_ == 0 {
            let mut v___x_2813_: u8 = 0;
            v___x_2813_ = 2;
            return v___x_2813_;
        } else {
            let mut v___x_2814_: u8 = 0;
            v___x_2814_ = 1;
            return v___x_2814_;
        }
    } else {
        let mut v___x_2815_: u8 = 0;
        v___x_2815_ = 0;
        return v___x_2815_;
    }
}
pub unsafe fn l_Lean_Server_wrapRpcProcedure___redArg___lam__0___boxed(
    mut v_x_2816_: *mut crate::leanh::LeanObject,
    mut v_y_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2818_: u64 = 0;
    let mut v_y_boxed_2819_: u64 = 0;
    let mut v_res_2820_: u8 = 0;
    let mut v_r_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2818_ = crate::leanh::lean_unbox_uint64(v_x_2816_);
    crate::leanh::lean_dec_ref(v_x_2816_);
    v_y_boxed_2819_ = crate::leanh::lean_unbox_uint64(v_y_2817_);
    crate::leanh::lean_dec_ref(v_y_2817_);
    v_res_2820_ =
        l_Lean_Server_wrapRpcProcedure___redArg___lam__0(v_x_boxed_2818_, v_y_boxed_2819_);
    v_r_2821_ = crate::leanh::lean_box((v_res_2820_) as usize);
    return v_r_2821_;
}
pub unsafe fn l_Lean_Server_wrapRpcProcedure___redArg___lam__1(
    mut v_expireTime_2822_: *mut crate::leanh::LeanObject,
    mut v_x_2823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2824_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2824_, 0, v_x_2823_);
    crate::leanh::lean_ctor_set(v___x_2824_, 1, v_expireTime_2822_);
    return v___x_2824_;
}
pub unsafe fn l_Lean_Server_wrapRpcProcedure___redArg___lam__2(
    mut v_val_2826_: *mut crate::leanh::LeanObject,
    mut v_inst_2827_: *mut crate::leanh::LeanObject,
    mut v_x_2828_: *mut crate::leanh::LeanObject,
    mut v___y_2829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2834_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2838_: u8 = 0;
    let mut v_a_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2842_: u8 = 0;
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rpcEncode_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objects_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expireTime_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2828_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2827_);
                    v_a_2831_ = crate::leanh::lean_ctor_get(v_x_2828_, 0);
                    v_isSharedCheck_2838_ = (!crate::leanh::lean_is_exclusive(v_x_2828_)) as u8;
                    if v_isSharedCheck_2838_ == 0 {
                        v___x_2833_ = v_x_2828_;
                        v_isShared_2834_ = v_isSharedCheck_2838_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2831_);
                        crate::leanh::lean_dec(v_x_2828_);
                        v___x_2833_ = crate::leanh::lean_box(0);
                        v_isShared_2834_ = v_isSharedCheck_2838_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2839_ = crate::leanh::lean_ctor_get(v_x_2828_, 0);
                    v_isSharedCheck_2857_ = (!crate::leanh::lean_is_exclusive(v_x_2828_)) as u8;
                    if v_isSharedCheck_2857_ == 0 {
                        v___x_2841_ = v_x_2828_;
                        v_isShared_2842_ = v_isSharedCheck_2857_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2839_);
                        crate::leanh::lean_dec(v_x_2828_);
                        v___x_2841_ = crate::leanh::lean_box(0);
                        v_isShared_2842_ = v_isSharedCheck_2857_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2834_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2833_, 1);
                    v___x_2836_ = v___x_2833_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
                    v___x_2836_ = v_reuseFailAlloc_2837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2836_;
            }
            3 => {
                v___x_2843_ = lean_st_ref_take(v_val_2826_);
                v_rpcEncode_2844_ = crate::leanh::lean_ctor_get(v_inst_2827_, 0);
                crate::leanh::lean_inc_ref(v_rpcEncode_2844_);
                crate::leanh::lean_dec_ref(v_inst_2827_);
                v_objects_2845_ = crate::leanh::lean_ctor_get(v___x_2843_, 0);
                crate::leanh::lean_inc_ref(v_objects_2845_);
                v_expireTime_2846_ = crate::leanh::lean_ctor_get(v___x_2843_, 1);
                crate::leanh::lean_inc(v_expireTime_2846_);
                crate::leanh::lean_dec(v___x_2843_);
                v___f_2847_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Server_wrapRpcProcedure___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2847_, 0, v_expireTime_2846_);
                v___x_2848_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__2___closed__0;
                v___x_2849_ =
                    crate::leanh::lean_apply_2(v_rpcEncode_2844_, v_a_2839_, v_objects_2845_);
                v___x_2850_ = l_Prod_map___redArg(v___x_2848_, v___f_2847_, v___x_2849_);
                v_fst_2851_ = crate::leanh::lean_ctor_get(v___x_2850_, 0);
                crate::leanh::lean_inc(v_fst_2851_);
                v_snd_2852_ = crate::leanh::lean_ctor_get(v___x_2850_, 1);
                crate::leanh::lean_inc(v_snd_2852_);
                crate::leanh::lean_dec_ref(v___x_2850_);
                v___x_2853_ = lean_st_ref_set(v_val_2826_, v_snd_2852_);
                if v_isShared_2842_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2841_, 0);
                    crate::leanh::lean_ctor_set(v___x_2841_, 0, v_fst_2851_);
                    v___x_2855_ = v___x_2841_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2856_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_fst_2851_);
                    v___x_2855_ = v_reuseFailAlloc_2856_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2855_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed(
    mut v_val_2858_: *mut crate::leanh::LeanObject,
    mut v_inst_2859_: *mut crate::leanh::LeanObject,
    mut v_x_2860_: *mut crate::leanh::LeanObject,
    mut v___y_2861_: *mut crate::leanh::LeanObject,
    mut v___y_2862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2863_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__2(
        v_val_2858_,
        v_inst_2859_,
        v_x_2860_,
        v___y_2861_,
    );
    crate::leanh::lean_dec_ref(v___y_2861_);
    crate::leanh::lean_dec(v_val_2858_);
    return v_res_2863_;
}
pub unsafe fn l_Lean_Server_wrapRpcProcedure___redArg___lam__3(
    mut v___f_2871_: *mut crate::leanh::LeanObject,
    mut v_inst_2872_: *mut crate::leanh::LeanObject,
    mut v_method_2873_: *mut crate::leanh::LeanObject,
    mut v_handler_2874_: *mut crate::leanh::LeanObject,
    mut v_inst_2875_: *mut crate::leanh::LeanObject,
    mut v_seshId_2876_: u64,
    mut v_j_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rpcSessions_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rpcDecode_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objects_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2891_: u8 = 0;
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut v_a_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2917_: u8 = 0;
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rpcSessions_2880_ = crate::leanh::lean_ctor_get(v___y_2878_, 0);
                v___x_2881_ = crate::leanh::lean_box_uint64(v_seshId_2876_);
                crate::leanh::lean_inc(v_rpcSessions_2880_);
                v___x_2882_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                    v___f_2871_,
                    v_rpcSessions_2880_,
                    v___x_2881_,
                );
                if crate::leanh::lean_obj_tag(v___x_2882_) == 1 {
                    v_val_2883_ = crate::leanh::lean_ctor_get(v___x_2882_, 0);
                    crate::leanh::lean_inc(v_val_2883_);
                    crate::leanh::lean_dec_ref_known(v___x_2882_, 1);
                    v___x_2884_ = lean_st_ref_get(v_val_2883_);
                    v_rpcDecode_2885_ = crate::leanh::lean_ctor_get(v_inst_2872_, 1);
                    crate::leanh::lean_inc_ref(v_rpcDecode_2885_);
                    crate::leanh::lean_dec_ref(v_inst_2872_);
                    v_objects_2886_ = crate::leanh::lean_ctor_get(v___x_2884_, 0);
                    crate::leanh::lean_inc_ref(v_objects_2886_);
                    crate::leanh::lean_dec(v___x_2884_);
                    crate::leanh::lean_inc(v_j_2877_);
                    v___x_2887_ =
                        crate::leanh::lean_apply_2(v_rpcDecode_2885_, v_j_2877_, v_objects_2886_);
                    if crate::leanh::lean_obj_tag(v___x_2887_) == 0 {
                        crate::leanh::lean_dec(v_val_2883_);
                        crate::leanh::lean_dec_ref(v_inst_2875_);
                        crate::leanh::lean_dec_ref(v_handler_2874_);
                        v_a_2888_ = crate::leanh::lean_ctor_get(v___x_2887_, 0);
                        v_isSharedCheck_2908_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2887_)) as u8;
                        if v_isSharedCheck_2908_ == 0 {
                            v___x_2890_ = v___x_2887_;
                            v_isShared_2891_ = v_isSharedCheck_2908_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2888_);
                            crate::leanh::lean_dec(v___x_2887_);
                            v___x_2890_ = crate::leanh::lean_box(0);
                            v_isShared_2891_ = v_isSharedCheck_2908_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_j_2877_);
                        crate::leanh::lean_dec(v_method_2873_);
                        v_a_2909_ = crate::leanh::lean_ctor_get(v___x_2887_, 0);
                        crate::leanh::lean_inc(v_a_2909_);
                        crate::leanh::lean_dec_ref_known(v___x_2887_, 1);
                        crate::leanh::lean_inc_ref(v___y_2878_);
                        v___x_2910_ = crate::leanh::lean_apply_3(
                            v_handler_2874_,
                            v_a_2909_,
                            v___y_2878_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_2910_) == 0 {
                            v_a_2911_ = crate::leanh::lean_ctor_get(v___x_2910_, 0);
                            crate::leanh::lean_inc(v_a_2911_);
                            crate::leanh::lean_dec_ref_known(v___x_2910_, 1);
                            v___f_2912_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Server_wrapRpcProcedure___redArg___lam__2___boxed
                                    as *mut core::ffi::c_void,
                                5,
                                2,
                            );
                            crate::leanh::lean_closure_set(v___f_2912_, 0, v_val_2883_);
                            crate::leanh::lean_closure_set(v___f_2912_, 1, v_inst_2875_);
                            v___x_2913_ = l_Lean_Server_RequestM_mapTaskCheap___redArg(
                                v_a_2911_,
                                v___f_2912_,
                                v___y_2878_,
                            );
                            return v___x_2913_;
                        } else {
                            crate::leanh::lean_dec(v_val_2883_);
                            crate::leanh::lean_dec_ref(v_inst_2875_);
                            v_a_2914_ = crate::leanh::lean_ctor_get(v___x_2910_, 0);
                            v_isSharedCheck_2921_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2910_)) as u8;
                            if v_isSharedCheck_2921_ == 0 {
                                v___x_2916_ = v___x_2910_;
                                v_isShared_2917_ = v_isSharedCheck_2921_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2914_);
                                crate::leanh::lean_dec(v___x_2910_);
                                v___x_2916_ = crate::leanh::lean_box(0);
                                v_isShared_2917_ = v_isSharedCheck_2921_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2882_);
                    crate::leanh::lean_dec(v_j_2877_);
                    crate::leanh::lean_dec_ref(v_inst_2875_);
                    crate::leanh::lean_dec_ref(v_handler_2874_);
                    crate::leanh::lean_dec(v_method_2873_);
                    crate::leanh::lean_dec_ref(v_inst_2872_);
                    v___x_2922_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__4;
                    v___x_2923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2923_, 0, v___x_2922_);
                    return v___x_2923_;
                }
            }
            1 => {
                v___x_2892_ = 3;
                v___x_2893_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__0;
                v___x_2894_ = 1;
                v___x_2895_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_method_2873_,
                    v___x_2894_,
                );
                v___x_2896_ = lean_string_append(v___x_2893_, v___x_2895_);
                crate::leanh::lean_dec_ref(v___x_2895_);
                v___x_2897_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__1;
                v___x_2898_ = lean_string_append(v___x_2896_, v___x_2897_);
                v___x_2899_ = l_Lean_Json_compress(v_j_2877_);
                v___x_2900_ = lean_string_append(v___x_2898_, v___x_2899_);
                crate::leanh::lean_dec_ref(v___x_2899_);
                v___x_2901_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3___closed__2;
                v___x_2902_ = lean_string_append(v___x_2900_, v___x_2901_);
                v___x_2903_ = lean_string_append(v___x_2902_, v_a_2888_);
                crate::leanh::lean_dec(v_a_2888_);
                v___x_2904_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2904_, 0, v___x_2903_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2904_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2892_,
                );
                if v_isShared_2891_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2890_, 1);
                    crate::leanh::lean_ctor_set(v___x_2890_, 0, v___x_2904_);
                    v___x_2906_ = v___x_2890_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2904_);
                    v___x_2906_ = v_reuseFailAlloc_2907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2906_;
            }
            3 => {
                if v_isShared_2917_ == 0 {
                    v___x_2919_ = v___x_2916_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2920_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
                    v___x_2919_ = v_reuseFailAlloc_2920_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed(
    mut v___f_2924_: *mut crate::leanh::LeanObject,
    mut v_inst_2925_: *mut crate::leanh::LeanObject,
    mut v_method_2926_: *mut crate::leanh::LeanObject,
    mut v_handler_2927_: *mut crate::leanh::LeanObject,
    mut v_inst_2928_: *mut crate::leanh::LeanObject,
    mut v_seshId_2929_: *mut crate::leanh::LeanObject,
    mut v_j_2930_: *mut crate::leanh::LeanObject,
    mut v___y_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_seshId_boxed_2933_: u64 = 0;
    let mut v_res_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_seshId_boxed_2933_ = crate::leanh::lean_unbox_uint64(v_seshId_2929_);
    crate::leanh::lean_dec_ref(v_seshId_2929_);
    v_res_2934_ = l_Lean_Server_wrapRpcProcedure___redArg___lam__3(
        v___f_2924_,
        v_inst_2925_,
        v_method_2926_,
        v_handler_2927_,
        v_inst_2928_,
        v_seshId_boxed_2933_,
        v_j_2930_,
        v___y_2931_,
    );
    crate::leanh::lean_dec_ref(v___y_2931_);
    return v_res_2934_;
}
pub unsafe fn l_Lean_Server_wrapRpcProcedure___redArg(
    mut v_method_2936_: *mut crate::leanh::LeanObject,
    mut v_inst_2937_: *mut crate::leanh::LeanObject,
    mut v_inst_2938_: *mut crate::leanh::LeanObject,
    mut v_handler_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2940_ = l_Lean_Server_wrapRpcProcedure___redArg___closed__0;
    v___f_2941_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_wrapRpcProcedure___redArg___lam__3___boxed as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2941_, 0, v___f_2940_);
    crate::leanh::lean_closure_set(v___f_2941_, 1, v_inst_2937_);
    crate::leanh::lean_closure_set(v___f_2941_, 2, v_method_2936_);
    crate::leanh::lean_closure_set(v___f_2941_, 3, v_handler_2939_);
    crate::leanh::lean_closure_set(v___f_2941_, 4, v_inst_2938_);
    return v___f_2941_;
}
pub unsafe fn l_Lean_Server_wrapRpcProcedure(
    mut v_method_2942_: *mut crate::leanh::LeanObject,
    mut v_paramType_2943_: *mut crate::leanh::LeanObject,
    mut v_respType_2944_: *mut crate::leanh::LeanObject,
    mut v_inst_2945_: *mut crate::leanh::LeanObject,
    mut v_inst_2946_: *mut crate::leanh::LeanObject,
    mut v_handler_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2948_ = l_Lean_Server_wrapRpcProcedure___redArg(
        v_method_2942_,
        v_inst_2945_,
        v_inst_2946_,
        v_handler_2947_,
    );
    return v___x_2948_;
}
pub unsafe fn l_Lean_Server_registerBuiltinRpcProcedure___redArg(
    mut v_method_2955_: *mut crate::leanh::LeanObject,
    mut v_inst_2956_: *mut crate::leanh::LeanObject,
    mut v_inst_2957_: *mut crate::leanh::LeanObject,
    mut v_handler_2958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errMsg_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: u8 = 0;
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v_a_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2960_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_2960_) == 0 {
                    v_a_2961_ = crate::leanh::lean_ctor_get(v___x_2960_, 0);
                    v_isSharedCheck_2996_ = (!crate::leanh::lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_2996_ == 0 {
                        v___x_2963_ = v___x_2960_;
                        v_isShared_2964_ = v_isSharedCheck_2996_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2961_);
                        crate::leanh::lean_dec(v___x_2960_);
                        v___x_2963_ = crate::leanh::lean_box(0);
                        v_isShared_2964_ = v_isSharedCheck_2996_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_handler_2958_);
                    crate::leanh::lean_dec_ref(v_inst_2957_);
                    crate::leanh::lean_dec_ref(v_inst_2956_);
                    crate::leanh::lean_dec(v_method_2955_);
                    v_a_2997_ = crate::leanh::lean_ctor_get(v___x_2960_, 0);
                    v_isSharedCheck_3004_ = (!crate::leanh::lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_3004_ == 0 {
                        v___x_2999_ = v___x_2960_;
                        v_isShared_3000_ = v_isSharedCheck_3004_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2997_);
                        crate::leanh::lean_dec(v___x_2960_);
                        v___x_2999_ = crate::leanh::lean_box(0);
                        v_isShared_3000_ = v_isSharedCheck_3004_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2965_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__0;
                v___x_2966_ = 1;
                crate::leanh::lean_inc(v_method_2955_);
                v___x_2967_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_method_2955_,
                    v___x_2966_,
                );
                v___x_2968_ = lean_string_append(v___x_2965_, v___x_2967_);
                crate::leanh::lean_dec_ref(v___x_2967_);
                v___x_2969_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1;
                v_errMsg_2970_ = lean_string_append(v___x_2968_, v___x_2969_);
                v___x_2971_ = (crate::leanh::lean_unbox(v_a_2961_) as u8);
                crate::leanh::lean_dec(v_a_2961_);
                if v___x_2971_ == 0 {
                    crate::leanh::lean_dec_ref(v_handler_2958_);
                    crate::leanh::lean_dec_ref(v_inst_2957_);
                    crate::leanh::lean_dec_ref(v_inst_2956_);
                    crate::leanh::lean_dec(v_method_2955_);
                    v___x_2972_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__2;
                    v___x_2973_ = lean_string_append(v_errMsg_2970_, v___x_2972_);
                    v___x_2974_ = lean_mk_io_user_error(v___x_2973_);
                    if v_isShared_2964_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2963_, 1);
                        crate::leanh::lean_ctor_set(v___x_2963_, 0, v___x_2974_);
                        v___x_2976_ = v___x_2963_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
                        v___x_2976_ = v_reuseFailAlloc_2977_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2978_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
                    v___x_2979_ = lean_st_ref_get(v___x_2978_);
                    v___x_2980_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__3;
                    v___x_2981_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__4;
                    crate::leanh::lean_inc(v_method_2955_);
                    v___x_2982_ = l_Lean_PersistentHashMap_contains___redArg(
                        v___x_2980_,
                        v___x_2981_,
                        v___x_2979_,
                        v_method_2955_,
                    );
                    if v___x_2982_ == 0 {
                        crate::leanh::lean_dec_ref(v_errMsg_2970_);
                        v___x_2983_ = lean_st_ref_take(v___x_2978_);
                        crate::leanh::lean_inc(v_method_2955_);
                        v___x_2984_ = l_Lean_Server_wrapRpcProcedure___redArg(
                            v_method_2955_,
                            v_inst_2956_,
                            v_inst_2957_,
                            v_handler_2958_,
                        );
                        v___x_2985_ = l_Lean_PersistentHashMap_insert___redArg(
                            v___x_2980_,
                            v___x_2981_,
                            v___x_2983_,
                            v_method_2955_,
                            v___x_2984_,
                        );
                        v___x_2986_ = lean_st_ref_set(v___x_2978_, v___x_2985_);
                        if v_isShared_2964_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2963_, 0, v___x_2986_);
                            v___x_2988_ = v___x_2963_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2989_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2986_);
                            v___x_2988_ = v_reuseFailAlloc_2989_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_handler_2958_);
                        crate::leanh::lean_dec_ref(v_inst_2957_);
                        crate::leanh::lean_dec_ref(v_inst_2956_);
                        crate::leanh::lean_dec(v_method_2955_);
                        v___x_2990_ =
                            l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5;
                        v___x_2991_ = lean_string_append(v_errMsg_2970_, v___x_2990_);
                        v___x_2992_ = lean_mk_io_user_error(v___x_2991_);
                        if v_isShared_2964_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2963_, 1);
                            crate::leanh::lean_ctor_set(v___x_2963_, 0, v___x_2992_);
                            v___x_2994_ = v___x_2963_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2995_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
                            v___x_2994_ = v_reuseFailAlloc_2995_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2976_;
            }
            3 => {
                return v___x_2988_;
            }
            4 => {
                return v___x_2994_;
            }
            5 => {
                if v_isShared_3000_ == 0 {
                    v___x_3002_ = v___x_2999_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3003_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
                    v___x_3002_ = v_reuseFailAlloc_3003_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerBuiltinRpcProcedure___redArg___boxed(
    mut v_method_3005_: *mut crate::leanh::LeanObject,
    mut v_inst_3006_: *mut crate::leanh::LeanObject,
    mut v_inst_3007_: *mut crate::leanh::LeanObject,
    mut v_handler_3008_: *mut crate::leanh::LeanObject,
    mut v_a_3009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(
        v_method_3005_,
        v_inst_3006_,
        v_inst_3007_,
        v_handler_3008_,
    );
    return v_res_3010_;
}
pub unsafe fn l_Lean_Server_registerBuiltinRpcProcedure(
    mut v_method_3011_: *mut crate::leanh::LeanObject,
    mut v_paramType_3012_: *mut crate::leanh::LeanObject,
    mut v_respType_3013_: *mut crate::leanh::LeanObject,
    mut v_inst_3014_: *mut crate::leanh::LeanObject,
    mut v_inst_3015_: *mut crate::leanh::LeanObject,
    mut v_handler_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3018_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg(
        v_method_3011_,
        v_inst_3014_,
        v_inst_3015_,
        v_handler_3016_,
    );
    return v___x_3018_;
}
pub unsafe fn l_Lean_Server_registerBuiltinRpcProcedure___boxed(
    mut v_method_3019_: *mut crate::leanh::LeanObject,
    mut v_paramType_3020_: *mut crate::leanh::LeanObject,
    mut v_respType_3021_: *mut crate::leanh::LeanObject,
    mut v_inst_3022_: *mut crate::leanh::LeanObject,
    mut v_inst_3023_: *mut crate::leanh::LeanObject,
    mut v_handler_3024_: *mut crate::leanh::LeanObject,
    mut v_a_3025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3026_ = l_Lean_Server_registerBuiltinRpcProcedure(
        v_method_3019_,
        v_paramType_3020_,
        v_respType_3021_,
        v_inst_3022_,
        v_inst_3023_,
        v_handler_3024_,
    );
    return v_res_3026_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(
    mut v_e_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3030_: u8 = 0;
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_unused_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3030_ = l_Lean_Expr_hasMVar(v_e_3027_);
                if v___x_3030_ == 0 {
                    v___x_3031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3031_, 0, v_e_3027_);
                    return v___x_3031_;
                } else {
                    v___x_3032_ = lean_st_ref_get(v___y_3028_);
                    v_mctx_3033_ = crate::leanh::lean_ctor_get(v___x_3032_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3033_);
                    crate::leanh::lean_dec(v___x_3032_);
                    v___x_3034_ = l_Lean_instantiateMVarsCore(v_mctx_3033_, v_e_3027_);
                    v_fst_3035_ = crate::leanh::lean_ctor_get(v___x_3034_, 0);
                    crate::leanh::lean_inc(v_fst_3035_);
                    v_snd_3036_ = crate::leanh::lean_ctor_get(v___x_3034_, 1);
                    crate::leanh::lean_inc(v_snd_3036_);
                    crate::leanh::lean_dec_ref(v___x_3034_);
                    v___x_3037_ = lean_st_ref_take(v___y_3028_);
                    v_cache_3038_ = crate::leanh::lean_ctor_get(v___x_3037_, 1);
                    v_zetaDeltaFVarIds_3039_ = crate::leanh::lean_ctor_get(v___x_3037_, 2);
                    v_postponed_3040_ = crate::leanh::lean_ctor_get(v___x_3037_, 3);
                    v_diag_3041_ = crate::leanh::lean_ctor_get(v___x_3037_, 4);
                    v_isSharedCheck_3050_ = (!crate::leanh::lean_is_exclusive(v___x_3037_)) as u8;
                    if v_isSharedCheck_3050_ == 0 {
                        v_unused_3051_ = crate::leanh::lean_ctor_get(v___x_3037_, 0);
                        crate::leanh::lean_dec(v_unused_3051_);
                        v___x_3043_ = v___x_3037_;
                        v_isShared_3044_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_3041_);
                        crate::leanh::lean_inc(v_postponed_3040_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3039_);
                        crate::leanh::lean_inc(v_cache_3038_);
                        crate::leanh::lean_dec(v___x_3037_);
                        v___x_3043_ = crate::leanh::lean_box(0);
                        v_isShared_3044_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3043_, 0, v_snd_3036_);
                    v___x_3046_ = v___x_3043_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_snd_3036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_cache_3038_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3049_,
                        2,
                        v_zetaDeltaFVarIds_3039_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 3, v_postponed_3040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 4, v_diag_3041_);
                    v___x_3046_ = v_reuseFailAlloc_3049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3047_ = lean_st_ref_set(v___y_3028_, v___x_3046_);
                v___x_3048_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3048_, 0, v_fst_3035_);
                return v___x_3048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg___boxed(
    mut v_e_3052_: *mut crate::leanh::LeanObject,
    mut v___y_3053_: *mut crate::leanh::LeanObject,
    mut v___y_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3055_ =
        l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(
            v_e_3052_,
            v___y_3053_,
        );
    crate::leanh::lean_dec(v___y_3053_);
    return v_res_3055_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(
    mut v_e_3056_: *mut crate::leanh::LeanObject,
    mut v___y_3057_: *mut crate::leanh::LeanObject,
    mut v___y_3058_: *mut crate::leanh::LeanObject,
    mut v___y_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3064_ =
        l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(
            v_e_3056_,
            v___y_3060_,
        );
    return v___x_3064_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___boxed(
    mut v_e_3065_: *mut crate::leanh::LeanObject,
    mut v___y_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
    mut v___y_3068_: *mut crate::leanh::LeanObject,
    mut v___y_3069_: *mut crate::leanh::LeanObject,
    mut v___y_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3073_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0(
        v_e_3065_,
        v___y_3066_,
        v___y_3067_,
        v___y_3068_,
        v___y_3069_,
        v___y_3070_,
        v___y_3071_,
    );
    crate::leanh::lean_dec(v___y_3071_);
    crate::leanh::lean_dec_ref(v___y_3070_);
    crate::leanh::lean_dec(v___y_3069_);
    crate::leanh::lean_dec_ref(v___y_3068_);
    crate::leanh::lean_dec(v___y_3067_);
    crate::leanh::lean_dec_ref(v___y_3066_);
    return v_res_3073_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(
    mut v_a_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
    mut v___y_3079_: *mut crate::leanh::LeanObject,
    mut v___y_3080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3082_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_3074_,
        v___y_3075_,
        v___y_3076_,
        v___y_3077_,
        v___y_3078_,
        v___y_3079_,
        v___y_3080_,
    );
    return v___x_3082_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg___boxed(
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
    mut v___y_3086_: *mut crate::leanh::LeanObject,
    mut v___y_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3091_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___redArg(v_a_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
    crate::leanh::lean_dec(v___y_3089_);
    crate::leanh::lean_dec_ref(v___y_3088_);
    crate::leanh::lean_dec(v___y_3087_);
    crate::leanh::lean_dec_ref(v___y_3086_);
    crate::leanh::lean_dec(v___y_3085_);
    crate::leanh::lean_dec_ref(v___y_3084_);
    return v_res_3091_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(
    mut v_00_u03b1_3092_: *mut crate::leanh::LeanObject,
    mut v_a_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
    mut v___y_3098_: *mut crate::leanh::LeanObject,
    mut v___y_3099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3101_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_3093_,
        v___y_3094_,
        v___y_3095_,
        v___y_3096_,
        v___y_3097_,
        v___y_3098_,
        v___y_3099_,
    );
    return v___x_3101_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed(
    mut v_00_u03b1_3102_: *mut crate::leanh::LeanObject,
    mut v_a_3103_: *mut crate::leanh::LeanObject,
    mut v___y_3104_: *mut crate::leanh::LeanObject,
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3111_ =
        l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1(
            v_00_u03b1_3102_,
            v_a_3103_,
            v___y_3104_,
            v___y_3105_,
            v___y_3106_,
            v___y_3107_,
            v___y_3108_,
            v___y_3109_,
        );
    crate::leanh::lean_dec(v___y_3109_);
    crate::leanh::lean_dec_ref(v___y_3108_);
    crate::leanh::lean_dec(v___y_3107_);
    crate::leanh::lean_dec_ref(v___y_3106_);
    crate::leanh::lean_dec(v___y_3105_);
    crate::leanh::lean_dec_ref(v___y_3104_);
    return v_res_3111_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3112_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3112_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3113_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0_once), _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__0);
    v___x_3114_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3114_, 0, v___x_3113_);
    return v___x_3114_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3115_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1_once), _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__1);
    v___x_3116_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3116_, 0, v___x_3115_);
    crate::leanh::lean_ctor_set(v___x_3116_, 1, v___x_3115_);
    return v___x_3116_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(
    mut v_env_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v_unused_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3120_ = lean_st_ref_take(v___y_3118_);
                v_nextMacroScope_3121_ = crate::leanh::lean_ctor_get(v___x_3120_, 1);
                v_ngen_3122_ = crate::leanh::lean_ctor_get(v___x_3120_, 2);
                v_auxDeclNGen_3123_ = crate::leanh::lean_ctor_get(v___x_3120_, 3);
                v_traceState_3124_ = crate::leanh::lean_ctor_get(v___x_3120_, 4);
                v_messages_3125_ = crate::leanh::lean_ctor_get(v___x_3120_, 6);
                v_infoState_3126_ = crate::leanh::lean_ctor_get(v___x_3120_, 7);
                v_snapshotTasks_3127_ = crate::leanh::lean_ctor_get(v___x_3120_, 8);
                v_isSharedCheck_3138_ = (!crate::leanh::lean_is_exclusive(v___x_3120_)) as u8;
                if v_isSharedCheck_3138_ == 0 {
                    v_unused_3139_ = crate::leanh::lean_ctor_get(v___x_3120_, 5);
                    crate::leanh::lean_dec(v_unused_3139_);
                    v_unused_3140_ = crate::leanh::lean_ctor_get(v___x_3120_, 0);
                    crate::leanh::lean_dec(v_unused_3140_);
                    v___x_3129_ = v___x_3120_;
                    v_isShared_3130_ = v_isSharedCheck_3138_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3127_);
                    crate::leanh::lean_inc(v_infoState_3126_);
                    crate::leanh::lean_inc(v_messages_3125_);
                    crate::leanh::lean_inc(v_traceState_3124_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3123_);
                    crate::leanh::lean_inc(v_ngen_3122_);
                    crate::leanh::lean_inc(v_nextMacroScope_3121_);
                    crate::leanh::lean_dec(v___x_3120_);
                    v___x_3129_ = crate::leanh::lean_box(0);
                    v_isShared_3130_ = v_isSharedCheck_3138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3131_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___closed__2);
                if v_isShared_3130_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3129_, 5, v___x_3131_);
                    crate::leanh::lean_ctor_set(v___x_3129_, 0, v_env_3117_);
                    v___x_3133_ = v___x_3129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3137_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_env_3117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_nextMacroScope_3121_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_ngen_3122_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 3, v_auxDeclNGen_3123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 4, v_traceState_3124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 5, v___x_3131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 6, v_messages_3125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 7, v_infoState_3126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 8, v_snapshotTasks_3127_);
                    v___x_3133_ = v_reuseFailAlloc_3137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3134_ = lean_st_ref_set(v___y_3118_, v___x_3133_);
                v___x_3135_ = crate::leanh::lean_box(0);
                v___x_3136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3136_, 0, v___x_3135_);
                return v___x_3136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg___boxed(
    mut v_env_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3144_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(
        v_env_3141_,
        v___y_3142_,
    );
    crate::leanh::lean_dec(v___y_3142_);
    return v_res_3144_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(
    mut v_env_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
    mut v___y_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3149_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(
        v_env_3145_,
        v___y_3147_,
    );
    return v___x_3149_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___boxed(
    mut v_env_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3154_ = l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2(
        v_env_3150_,
        v___y_3151_,
        v___y_3152_,
    );
    crate::leanh::lean_dec(v___y_3152_);
    crate::leanh::lean_dec_ref(v___y_3151_);
    return v_res_3154_;
}
pub unsafe fn l_Lean_Server_registerRpcProcedure___lam__0(
    mut v_x_3155_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3156_: u8 = 0;
    v___x_3156_ = 0;
    return v___x_3156_;
}
pub unsafe fn l_Lean_Server_registerRpcProcedure___lam__0___boxed(
    mut v_x_3157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3158_: u8 = 0;
    let mut v_r_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3158_ = l_Lean_Server_registerRpcProcedure___lam__0(v_x_3157_);
    crate::leanh::lean_dec(v_x_3157_);
    v_r_3159_ = crate::leanh::lean_box((v_res_3158_) as usize);
    return v_r_3159_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3164_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__3;
    v___x_3165_ = l_String_toRawSubstring_x27(v___x_3164_);
    return v___x_3165_;
}
pub unsafe fn l_Lean_Server_registerRpcProcedure___lam__1(
    mut v___x_3176_: u8,
    mut v___x_3177_: *mut crate::leanh::LeanObject,
    mut v___x_3178_: *mut crate::leanh::LeanObject,
    mut v_method_3179_: *mut crate::leanh::LeanObject,
    mut v___x_3180_: *mut crate::leanh::LeanObject,
    mut v___x_3181_: u8,
    mut v___y_3182_: *mut crate::leanh::LeanObject,
    mut v___y_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3189_ = crate::leanh::lean_ctor_get(v___y_3186_, 5);
                v_quotContext_3190_ = crate::leanh::lean_ctor_get(v___y_3186_, 10);
                v_currMacroScope_3191_ = crate::leanh::lean_ctor_get(v___y_3186_, 11);
                v___x_3192_ = l_Lean_SourceInfo_fromRef(v_ref_3189_, v___x_3176_);
                v___x_3193_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__0;
                v___x_3194_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__1;
                v___x_3195_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__2;
                crate::leanh::lean_inc_ref_n(v___x_3177_, 2);
                v___x_3196_ =
                    l_Lean_Name_mkStr4(v___x_3177_, v___x_3193_, v___x_3194_, v___x_3195_);
                v___x_3197_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__3;
                v___x_3198_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_registerRpcProcedure___lam__1___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_registerRpcProcedure___lam__1___closed__4_once
                    ),
                    _init_l_Lean_Server_registerRpcProcedure___lam__1___closed__4,
                );
                v___x_3199_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__5;
                crate::leanh::lean_inc(v_currMacroScope_3191_);
                crate::leanh::lean_inc(v_quotContext_3190_);
                v___x_3200_ =
                    l_Lean_addMacroScope(v_quotContext_3190_, v___x_3199_, v_currMacroScope_3191_);
                v___x_3201_ = l_Lean_Name_mkStr3(v___x_3177_, v___x_3178_, v___x_3197_);
                v___x_3202_ = crate::leanh::lean_box(0);
                v___x_3203_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3203_, 0, v___x_3201_);
                crate::leanh::lean_ctor_set(v___x_3203_, 1, v___x_3202_);
                v___x_3204_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3204_, 0, v___x_3203_);
                crate::leanh::lean_ctor_set(v___x_3204_, 1, v___x_3202_);
                crate::leanh::lean_inc(v___x_3192_);
                v___x_3205_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3205_, 0, v___x_3192_);
                crate::leanh::lean_ctor_set(v___x_3205_, 1, v___x_3198_);
                crate::leanh::lean_ctor_set(v___x_3205_, 2, v___x_3200_);
                crate::leanh::lean_ctor_set(v___x_3205_, 3, v___x_3204_);
                v___x_3206_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__7;
                crate::leanh::lean_inc(v_method_3179_);
                v___x_3221_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_3202_,
                    v_method_3179_,
                );
                if crate::leanh::lean_obj_tag(v___x_3221_) == 0 {
                    crate::leanh::lean_inc(v_method_3179_);
                    v___x_3222_ = l_Lean_quoteNameMk(v_method_3179_);
                    v___y_3208_ = v___x_3222_;
                    state = 1;
                    continue;
                } else {
                    v_val_3223_ = crate::leanh::lean_ctor_get(v___x_3221_, 0);
                    crate::leanh::lean_inc(v_val_3223_);
                    crate::leanh::lean_dec_ref_known(v___x_3221_, 1);
                    v___x_3224_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__10;
                    crate::leanh::lean_inc_ref(v___x_3177_);
                    v___x_3225_ =
                        l_Lean_Name_mkStr4(v___x_3177_, v___x_3193_, v___x_3194_, v___x_3224_);
                    v___x_3226_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__11;
                    v___x_3227_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__12;
                    v___x_3228_ = lean_string_intercalate(v___x_3227_, v_val_3223_);
                    v___x_3229_ = lean_string_append(v___x_3226_, v___x_3228_);
                    crate::leanh::lean_dec_ref(v___x_3228_);
                    v___x_3230_ = crate::leanh::lean_box(2);
                    v___x_3231_ = l_Lean_Syntax_mkNameLit(v___x_3229_, v___x_3230_);
                    v___x_3232_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3233_ = lean_mk_empty_array_with_capacity(v___x_3232_);
                    v___x_3234_ = lean_array_push(v___x_3233_, v___x_3231_);
                    v___x_3235_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3235_, 0, v___x_3230_);
                    crate::leanh::lean_ctor_set(v___x_3235_, 1, v___x_3225_);
                    crate::leanh::lean_ctor_set(v___x_3235_, 2, v___x_3234_);
                    v___y_3208_ = v___x_3235_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3209_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__8;
                v___x_3210_ =
                    l_Lean_Name_mkStr4(v___x_3177_, v___x_3193_, v___x_3194_, v___x_3209_);
                v___x_3211_ = l_Lean_Server_registerRpcProcedure___lam__1___closed__9;
                crate::leanh::lean_inc_n(v___x_3192_, 3);
                v___x_3212_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3212_, 0, v___x_3192_);
                crate::leanh::lean_ctor_set(v___x_3212_, 1, v___x_3211_);
                v___x_3213_ = l_Lean_Syntax_node1(v___x_3192_, v___x_3210_, v___x_3212_);
                v___x_3214_ = lean_mk_syntax_ident(v_method_3179_);
                crate::leanh::lean_inc(v___x_3213_);
                v___x_3215_ = l_Lean_Syntax_node4(
                    v___x_3192_,
                    v___x_3206_,
                    v___y_3208_,
                    v___x_3213_,
                    v___x_3213_,
                    v___x_3214_,
                );
                v___x_3216_ =
                    l_Lean_Syntax_node2(v___x_3192_, v___x_3196_, v___x_3205_, v___x_3215_);
                v___x_3217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3217_, 0, v___x_3180_);
                v___x_3218_ = l_Lean_Elab_Term_elabTerm(
                    v___x_3216_,
                    v___x_3217_,
                    v___x_3181_,
                    v___x_3181_,
                    v___y_3182_,
                    v___y_3183_,
                    v___y_3184_,
                    v___y_3185_,
                    v___y_3186_,
                    v___y_3187_,
                );
                crate::leanh::lean_dec_ref(v___y_3186_);
                if crate::leanh::lean_obj_tag(v___x_3218_) == 0 {
                    v_a_3219_ = crate::leanh::lean_ctor_get(v___x_3218_, 0);
                    crate::leanh::lean_inc(v_a_3219_);
                    crate::leanh::lean_dec_ref_known(v___x_3218_, 1);
                    v___x_3220_ = l_Lean_instantiateMVars___at___00Lean_Server_registerRpcProcedure_spec__0___redArg(v_a_3219_, v___y_3185_);
                    return v___x_3220_;
                } else {
                    return v___x_3218_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerRpcProcedure___lam__1___boxed(
    mut v___x_3236_: *mut crate::leanh::LeanObject,
    mut v___x_3237_: *mut crate::leanh::LeanObject,
    mut v___x_3238_: *mut crate::leanh::LeanObject,
    mut v_method_3239_: *mut crate::leanh::LeanObject,
    mut v___x_3240_: *mut crate::leanh::LeanObject,
    mut v___x_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6267__boxed_3249_: u8 = 0;
    let mut v___x_6271__boxed_3250_: u8 = 0;
    let mut v_res_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6267__boxed_3249_ = (crate::leanh::lean_unbox(v___x_3236_) as u8);
    v___x_6271__boxed_3250_ = (crate::leanh::lean_unbox(v___x_3241_) as u8);
    v_res_3251_ = l_Lean_Server_registerRpcProcedure___lam__1(
        v___x_6267__boxed_3249_,
        v___x_3237_,
        v___x_3238_,
        v_method_3239_,
        v___x_3240_,
        v___x_6271__boxed_3250_,
        v___y_3242_,
        v___y_3243_,
        v___y_3244_,
        v___y_3245_,
        v___y_3246_,
        v___y_3247_,
    );
    crate::leanh::lean_dec(v___y_3247_);
    crate::leanh::lean_dec(v___y_3245_);
    crate::leanh::lean_dec_ref(v___y_3244_);
    crate::leanh::lean_dec(v___y_3243_);
    crate::leanh::lean_dec_ref(v___y_3242_);
    return v_res_3251_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3252_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3252_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__0);
    v___x_3254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3254_, 0, v___x_3253_);
    return v___x_3254_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3255_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1);
    v___x_3256_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3257_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3257_, 0, v___x_3256_);
    crate::leanh::lean_ctor_set(v___x_3257_, 1, v___x_3256_);
    crate::leanh::lean_ctor_set(v___x_3257_, 2, v___x_3256_);
    crate::leanh::lean_ctor_set(v___x_3257_, 3, v___x_3256_);
    crate::leanh::lean_ctor_set(v___x_3257_, 4, v___x_3255_);
    crate::leanh::lean_ctor_set(v___x_3257_, 5, v___x_3255_);
    crate::leanh::lean_ctor_set(v___x_3257_, 6, v___x_3255_);
    crate::leanh::lean_ctor_set(v___x_3257_, 7, v___x_3255_);
    crate::leanh::lean_ctor_set(v___x_3257_, 8, v___x_3255_);
    crate::leanh::lean_ctor_set(v___x_3257_, 9, v___x_3255_);
    return v___x_3257_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3259_ = lean_mk_empty_array_with_capacity(v___x_3258_);
    v___x_3260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3259_);
    return v___x_3260_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3261_: usize = 0;
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3261_ = 5usize;
    v___x_3262_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3263_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3264_ = lean_mk_empty_array_with_capacity(v___x_3263_);
    v___x_3265_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__3);
    v___x_3266_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3266_, 0, v___x_3265_);
    crate::leanh::lean_ctor_set(v___x_3266_, 1, v___x_3264_);
    crate::leanh::lean_ctor_set(v___x_3266_, 2, v___x_3262_);
    crate::leanh::lean_ctor_set(v___x_3266_, 3, v___x_3262_);
    crate::leanh::lean_ctor_set_usize(v___x_3266_, 4, v___x_3261_);
    return v___x_3266_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3267_ = crate::leanh::lean_box(1);
    v___x_3268_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
    v___x_3269_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__1);
    v___x_3270_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3270_, 0, v___x_3269_);
    crate::leanh::lean_ctor_set(v___x_3270_, 1, v___x_3268_);
    crate::leanh::lean_ctor_set(v___x_3270_, 2, v___x_3267_);
    return v___x_3270_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(
    mut v_msgData_3271_: *mut crate::leanh::LeanObject,
    mut v___y_3272_: *mut crate::leanh::LeanObject,
    mut v___y_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3275_ = lean_st_ref_get(v___y_3273_);
    v_env_3276_ = crate::leanh::lean_ctor_get(v___x_3275_, 0);
    crate::leanh::lean_inc_ref(v_env_3276_);
    crate::leanh::lean_dec(v___x_3275_);
    v_options_3277_ = crate::leanh::lean_ctor_get(v___y_3272_, 2);
    v___x_3278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__2);
    v___x_3279_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__5);
    crate::leanh::lean_inc_ref(v_options_3277_);
    v___x_3280_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3280_, 0, v_env_3276_);
    crate::leanh::lean_ctor_set(v___x_3280_, 1, v___x_3278_);
    crate::leanh::lean_ctor_set(v___x_3280_, 2, v___x_3279_);
    crate::leanh::lean_ctor_set(v___x_3280_, 3, v_options_3277_);
    v___x_3281_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3281_, 0, v___x_3280_);
    crate::leanh::lean_ctor_set(v___x_3281_, 1, v_msgData_3271_);
    v___x_3282_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3282_, 0, v___x_3281_);
    return v___x_3282_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___boxed(
    mut v_msgData_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
    mut v___y_3285_: *mut crate::leanh::LeanObject,
    mut v___y_3286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3287_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msgData_3283_, v___y_3284_, v___y_3285_);
    crate::leanh::lean_dec(v___y_3285_);
    crate::leanh::lean_dec_ref(v___y_3284_);
    return v_res_3287_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(
    mut v_msg_3288_: *mut crate::leanh::LeanObject,
    mut v___y_3289_: *mut crate::leanh::LeanObject,
    mut v___y_3290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3297_: u8 = 0;
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3292_ = crate::leanh::lean_ctor_get(v___y_3289_, 5);
                v___x_3293_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3(v_msg_3288_, v___y_3289_, v___y_3290_);
                v_a_3294_ = crate::leanh::lean_ctor_get(v___x_3293_, 0);
                v_isSharedCheck_3302_ = (!crate::leanh::lean_is_exclusive(v___x_3293_)) as u8;
                if v_isSharedCheck_3302_ == 0 {
                    v___x_3296_ = v___x_3293_;
                    v_isShared_3297_ = v_isSharedCheck_3302_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3294_);
                    crate::leanh::lean_dec(v___x_3293_);
                    v___x_3296_ = crate::leanh::lean_box(0);
                    v_isShared_3297_ = v_isSharedCheck_3302_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3292_);
                v___x_3298_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3298_, 0, v_ref_3292_);
                crate::leanh::lean_ctor_set(v___x_3298_, 1, v_a_3294_);
                if v_isShared_3297_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3296_, 1);
                    crate::leanh::lean_ctor_set(v___x_3296_, 0, v___x_3298_);
                    v___x_3300_ = v___x_3296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
                    v___x_3300_ = v_reuseFailAlloc_3301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg___boxed(
    mut v_msg_3303_: *mut crate::leanh::LeanObject,
    mut v___y_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(
        v_msg_3303_,
        v___y_3304_,
        v___y_3305_,
    );
    crate::leanh::lean_dec(v___y_3305_);
    crate::leanh::lean_dec_ref(v___y_3304_);
    return v_res_3307_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__4() -> u64 {
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: u64 = 0;
    v___x_3325_ = l_Lean_Server_registerRpcProcedure___closed__3;
    v___x_3326_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3325_);
    return v___x_3326_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3327_: u64 = 0;
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__4_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__4,
    );
    v___x_3328_ = l_Lean_Server_registerRpcProcedure___closed__3;
    v___x_3329_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_3329_, 0, v___x_3328_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_3329_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3327_,
    );
    return v___x_3329_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3330_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3330_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3331_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__6_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__6,
    );
    v___x_3332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3332_, 0, v___x_3331_);
    return v___x_3332_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3333_ = crate::leanh::lean_box(1);
    v___x_3334_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
    v___x_3335_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__7,
    );
    v___x_3336_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3336_, 0, v___x_3335_);
    crate::leanh::lean_ctor_set(v___x_3336_, 1, v___x_3334_);
    crate::leanh::lean_ctor_set(v___x_3336_, 2, v___x_3333_);
    return v___x_3336_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3337_ = 1;
    v___x_3338_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3339_ = crate::leanh::lean_box(0);
    v___x_3340_ = l_Lean_Server_registerRpcProcedure___closed__1;
    v___x_3341_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__8_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__8,
    );
    v___x_3342_ = crate::leanh::lean_box(1);
    v___x_3343_ = 0;
    v___x_3344_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__5_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__5,
    );
    v___x_3345_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_3345_, 0, v___x_3344_);
    crate::leanh::lean_ctor_set(v___x_3345_, 1, v___x_3342_);
    crate::leanh::lean_ctor_set(v___x_3345_, 2, v___x_3341_);
    crate::leanh::lean_ctor_set(v___x_3345_, 3, v___x_3340_);
    crate::leanh::lean_ctor_set(v___x_3345_, 4, v___x_3339_);
    crate::leanh::lean_ctor_set(v___x_3345_, 5, v___x_3338_);
    crate::leanh::lean_ctor_set(v___x_3345_, 6, v___x_3339_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3345_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v___x_3343_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3345_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v___x_3343_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3345_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v___x_3343_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3345_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v___x_3337_,
    );
    return v___x_3345_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3346_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__7,
    );
    v___x_3347_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3348_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3348_, 0, v___x_3347_);
    crate::leanh::lean_ctor_set(v___x_3348_, 1, v___x_3347_);
    crate::leanh::lean_ctor_set(v___x_3348_, 2, v___x_3347_);
    crate::leanh::lean_ctor_set(v___x_3348_, 3, v___x_3347_);
    crate::leanh::lean_ctor_set(v___x_3348_, 4, v___x_3346_);
    crate::leanh::lean_ctor_set(v___x_3348_, 5, v___x_3346_);
    crate::leanh::lean_ctor_set(v___x_3348_, 6, v___x_3346_);
    crate::leanh::lean_ctor_set(v___x_3348_, 7, v___x_3346_);
    crate::leanh::lean_ctor_set(v___x_3348_, 8, v___x_3346_);
    crate::leanh::lean_ctor_set(v___x_3348_, 9, v___x_3346_);
    return v___x_3348_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3349_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__7,
    );
    v___x_3350_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3350_, 0, v___x_3349_);
    crate::leanh::lean_ctor_set(v___x_3350_, 1, v___x_3349_);
    crate::leanh::lean_ctor_set(v___x_3350_, 2, v___x_3349_);
    crate::leanh::lean_ctor_set(v___x_3350_, 3, v___x_3349_);
    crate::leanh::lean_ctor_set(v___x_3350_, 4, v___x_3349_);
    crate::leanh::lean_ctor_set(v___x_3350_, 5, v___x_3349_);
    return v___x_3350_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3351_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__7,
    );
    v___x_3352_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3351_);
    crate::leanh::lean_ctor_set(v___x_3352_, 1, v___x_3351_);
    crate::leanh::lean_ctor_set(v___x_3352_, 2, v___x_3351_);
    crate::leanh::lean_ctor_set(v___x_3352_, 3, v___x_3351_);
    crate::leanh::lean_ctor_set(v___x_3352_, 4, v___x_3351_);
    return v___x_3352_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3353_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__12_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__12,
    );
    v___x_3354_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3_spec__3___closed__4);
    v___x_3355_ = crate::leanh::lean_box(1);
    v___x_3356_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__11_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__11,
    );
    v___x_3357_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__10_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__10,
    );
    v___x_3358_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3358_, 0, v___x_3357_);
    crate::leanh::lean_ctor_set(v___x_3358_, 1, v___x_3356_);
    crate::leanh::lean_ctor_set(v___x_3358_, 2, v___x_3355_);
    crate::leanh::lean_ctor_set(v___x_3358_, 3, v___x_3354_);
    crate::leanh::lean_ctor_set(v___x_3358_, 4, v___x_3353_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3359_ = crate::leanh::lean_box(0);
    v___x_3360_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_evalRpcProcedureUnsafe___closed__1;
    v___x_3361_ = l_Lean_mkConst(v___x_3360_, v___x_3359_);
    return v___x_3361_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3368_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__7_once),
        _init_l_Lean_Server_registerRpcProcedure___closed__7,
    );
    v___x_3369_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3369_, 0, v___x_3368_);
    crate::leanh::lean_ctor_set(v___x_3369_, 1, v___x_3368_);
    return v___x_3369_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3371_ = l_Lean_Server_registerRpcProcedure___closed__19;
    v___x_3372_ = l_Lean_stringToMessageData(v___x_3371_);
    return v___x_3372_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3373_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__1;
    v___x_3374_ = l_Lean_stringToMessageData(v___x_3373_);
    return v___x_3374_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3375_ = l_Lean_Server_registerBuiltinRpcProcedure___redArg___closed__5;
    v___x_3376_ = l_Lean_stringToMessageData(v___x_3375_);
    return v___x_3376_;
}
pub unsafe fn _init_l_Lean_Server_registerRpcProcedure___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3378_ = l_Lean_Server_registerRpcProcedure___closed__23;
    v___x_3379_ = l_Lean_stringToMessageData(v___x_3378_);
    return v___x_3379_;
}
pub unsafe fn l_Lean_Server_registerRpcProcedure(
    mut v_method_3380_: *mut crate::leanh::LeanObject,
    mut v_a_3381_: *mut crate::leanh::LeanObject,
    mut v_a_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3412_: u8 = 0;
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3434_: u8 = 0;
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v_unused_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3450_: u8 = 0;
    let mut v_unused_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3455_: u8 = 0;
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: u8 = 0;
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3384_ = lean_st_ref_get(v_a_3382_);
                v___x_3385_ =
                    l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures;
                v___x_3386_ = lean_st_ref_get(v___x_3385_);
                v_env_3387_ = crate::leanh::lean_ctor_get(v___x_3384_, 0);
                crate::leanh::lean_inc_ref(v_env_3387_);
                crate::leanh::lean_dec(v___x_3384_);
                v___x_3460_ = crate::leanh::lean_box(0);
                v___x_3461_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__20),
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__20_once),
                    _init_l_Lean_Server_registerRpcProcedure___closed__20,
                );
                crate::leanh::lean_inc(v_method_3380_);
                v___x_3462_ = l_Lean_MessageData_ofName(v_method_3380_);
                v___x_3463_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3463_, 0, v___x_3461_);
                crate::leanh::lean_ctor_set(v___x_3463_, 1, v___x_3462_);
                v___x_3464_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__21),
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__21_once),
                    _init_l_Lean_Server_registerRpcProcedure___closed__21,
                );
                v___x_3465_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3465_, 0, v___x_3463_);
                crate::leanh::lean_ctor_set(v___x_3465_, 1, v___x_3464_);
                v___x_3474_ = l_Lean_PersistentHashMap_contains___at___00Lean_Server_existsBuiltinRpcProcedure_spec__0___redArg(v___x_3386_, v_method_3380_);
                crate::leanh::lean_dec(v___x_3386_);
                if v___x_3474_ == 0 {
                    v___y_3467_ = v_a_3381_;
                    v___y_3468_ = v_a_3382_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_3387_);
                    crate::leanh::lean_dec(v_method_3380_);
                    v___x_3475_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__24),
                        core::ptr::addr_of_mut!(
                            l_Lean_Server_registerRpcProcedure___closed__24_once
                        ),
                        _init_l_Lean_Server_registerRpcProcedure___closed__24,
                    );
                    v___x_3476_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3476_, 0, v___x_3465_);
                    crate::leanh::lean_ctor_set(v___x_3476_, 1, v___x_3475_);
                    v___x_3477_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_3476_, v_a_3381_, v_a_3382_);
                    return v___x_3477_;
                }
            }
            1 => {
                v___x_3391_ = crate::leanh::lean_box(0);
                v___x_3392_ = 1;
                v___x_3393_ = 0;
                v___x_3394_ = l_Lean_Server_registerRpcProcedure___closed__2;
                v___x_3395_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__9_once),
                    _init_l_Lean_Server_registerRpcProcedure___closed__9,
                );
                v___x_3396_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__13_once),
                    _init_l_Lean_Server_registerRpcProcedure___closed__13,
                );
                v___x_3397_ = lean_st_mk_ref(v___x_3396_);
                v___x_3398_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_;
                v___x_3399_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_;
                v___x_3400_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__14_once),
                    _init_l_Lean_Server_registerRpcProcedure___closed__14,
                );
                v___x_3401_ = crate::leanh::lean_box((v___x_3393_) as usize);
                v___x_3402_ = crate::leanh::lean_box((v___x_3392_) as usize);
                crate::leanh::lean_inc(v_method_3380_);
                v___f_3403_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Server_registerRpcProcedure___lam__1___boxed as *mut core::ffi::c_void,
                    13,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_3403_, 0, v___x_3401_);
                crate::leanh::lean_closure_set(v___f_3403_, 1, v___x_3398_);
                crate::leanh::lean_closure_set(v___f_3403_, 2, v___x_3399_);
                crate::leanh::lean_closure_set(v___f_3403_, 3, v_method_3380_);
                crate::leanh::lean_closure_set(v___f_3403_, 4, v___x_3400_);
                crate::leanh::lean_closure_set(v___f_3403_, 5, v___x_3402_);
                v___x_3404_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Server_registerRpcProcedure_spec__1___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___x_3404_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3404_, 1, v___f_3403_);
                v___x_3405_ = l_Lean_Server_registerRpcProcedure___closed__15;
                v___x_3406_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                    v___x_3404_,
                    v___x_3394_,
                    v___x_3405_,
                    v___x_3395_,
                    v___x_3397_,
                    v___y_3389_,
                    v___y_3390_,
                );
                if crate::leanh::lean_obj_tag(v___x_3406_) == 0 {
                    v_a_3407_ = crate::leanh::lean_ctor_get(v___x_3406_, 0);
                    crate::leanh::lean_inc(v_a_3407_);
                    crate::leanh::lean_dec_ref_known(v___x_3406_, 1);
                    v___x_3408_ = lean_st_ref_get(v___x_3397_);
                    crate::leanh::lean_dec(v___x_3397_);
                    crate::leanh::lean_dec(v___x_3408_);
                    v_fst_3409_ = crate::leanh::lean_ctor_get(v_a_3407_, 0);
                    v_isSharedCheck_3450_ = (!crate::leanh::lean_is_exclusive(v_a_3407_)) as u8;
                    if v_isSharedCheck_3450_ == 0 {
                        v_unused_3451_ = crate::leanh::lean_ctor_get(v_a_3407_, 1);
                        crate::leanh::lean_dec(v_unused_3451_);
                        v___x_3411_ = v_a_3407_;
                        v_isShared_3412_ = v_isSharedCheck_3450_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3409_);
                        crate::leanh::lean_dec(v_a_3407_);
                        v___x_3411_ = crate::leanh::lean_box(0);
                        v_isShared_3412_ = v_isSharedCheck_3450_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3397_);
                    crate::leanh::lean_dec(v_method_3380_);
                    v_a_3452_ = crate::leanh::lean_ctor_get(v___x_3406_, 0);
                    v_isSharedCheck_3459_ = (!crate::leanh::lean_is_exclusive(v___x_3406_)) as u8;
                    if v_isSharedCheck_3459_ == 0 {
                        v___x_3454_ = v___x_3406_;
                        v_isShared_3455_ = v_isSharedCheck_3459_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3452_);
                        crate::leanh::lean_dec(v___x_3406_);
                        v___x_3454_ = crate::leanh::lean_box(0);
                        v_isShared_3455_ = v_isSharedCheck_3459_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3413_ = l_Lean_Server_registerRpcProcedure___closed__17;
                crate::leanh::lean_inc(v_method_3380_);
                v___x_3414_ = l_Lean_Name_append(v_method_3380_, v___x_3413_);
                crate::leanh::lean_inc_n(v___x_3414_, 2);
                v___x_3415_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3415_, 0, v___x_3414_);
                crate::leanh::lean_ctor_set(v___x_3415_, 1, v___x_3391_);
                crate::leanh::lean_ctor_set(v___x_3415_, 2, v___x_3400_);
                v___x_3416_ = crate::leanh::lean_box(0);
                v___x_3417_ = 1;
                if v_isShared_3412_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3411_, 1);
                    crate::leanh::lean_ctor_set(v___x_3411_, 1, v___x_3391_);
                    crate::leanh::lean_ctor_set(v___x_3411_, 0, v___x_3414_);
                    v___x_3419_ = v___x_3411_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3449_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3391_);
                    v___x_3419_ = v_reuseFailAlloc_3449_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3420_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3420_, 0, v___x_3415_);
                crate::leanh::lean_ctor_set(v___x_3420_, 1, v_fst_3409_);
                crate::leanh::lean_ctor_set(v___x_3420_, 2, v___x_3416_);
                crate::leanh::lean_ctor_set(v___x_3420_, 3, v___x_3419_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3420_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___x_3417_,
                );
                v___x_3421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3421_, 0, v___x_3420_);
                crate::leanh::lean_inc_ref(v___x_3421_);
                v___x_3422_ = l_Lean_addDecl(v___x_3421_, v___x_3393_, v___y_3389_, v___y_3390_);
                if crate::leanh::lean_obj_tag(v___x_3422_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3422_, 1);
                    v___x_3423_ = lean_st_ref_take(v___y_3390_);
                    v_env_3424_ = crate::leanh::lean_ctor_get(v___x_3423_, 0);
                    v_nextMacroScope_3425_ = crate::leanh::lean_ctor_get(v___x_3423_, 1);
                    v_ngen_3426_ = crate::leanh::lean_ctor_get(v___x_3423_, 2);
                    v_auxDeclNGen_3427_ = crate::leanh::lean_ctor_get(v___x_3423_, 3);
                    v_traceState_3428_ = crate::leanh::lean_ctor_get(v___x_3423_, 4);
                    v_messages_3429_ = crate::leanh::lean_ctor_get(v___x_3423_, 6);
                    v_infoState_3430_ = crate::leanh::lean_ctor_get(v___x_3423_, 7);
                    v_snapshotTasks_3431_ = crate::leanh::lean_ctor_get(v___x_3423_, 8);
                    v_isSharedCheck_3447_ = (!crate::leanh::lean_is_exclusive(v___x_3423_)) as u8;
                    if v_isSharedCheck_3447_ == 0 {
                        v_unused_3448_ = crate::leanh::lean_ctor_get(v___x_3423_, 5);
                        crate::leanh::lean_dec(v_unused_3448_);
                        v___x_3433_ = v___x_3423_;
                        v_isShared_3434_ = v_isSharedCheck_3447_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_3431_);
                        crate::leanh::lean_inc(v_infoState_3430_);
                        crate::leanh::lean_inc(v_messages_3429_);
                        crate::leanh::lean_inc(v_traceState_3428_);
                        crate::leanh::lean_inc(v_auxDeclNGen_3427_);
                        crate::leanh::lean_inc(v_ngen_3426_);
                        crate::leanh::lean_inc(v_nextMacroScope_3425_);
                        crate::leanh::lean_inc(v_env_3424_);
                        crate::leanh::lean_dec(v___x_3423_);
                        v___x_3433_ = crate::leanh::lean_box(0);
                        v_isShared_3434_ = v_isSharedCheck_3447_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3421_, 1);
                    crate::leanh::lean_dec(v___x_3414_);
                    crate::leanh::lean_dec(v_method_3380_);
                    return v___x_3422_;
                }
            }
            4 => {
                crate::leanh::lean_inc(v___x_3414_);
                v___x_3435_ = l_Lean_markMeta(v_env_3424_, v___x_3414_);
                v___x_3436_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__18_once),
                    _init_l_Lean_Server_registerRpcProcedure___closed__18,
                );
                if v_isShared_3434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3433_, 5, v___x_3436_);
                    crate::leanh::lean_ctor_set(v___x_3433_, 0, v___x_3435_);
                    v___x_3438_ = v___x_3433_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_nextMacroScope_3425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 2, v_ngen_3426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 3, v_auxDeclNGen_3427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 4, v_traceState_3428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 5, v___x_3436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 6, v_messages_3429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 7, v_infoState_3430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 8, v_snapshotTasks_3431_);
                    v___x_3438_ = v_reuseFailAlloc_3446_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3439_ = lean_st_ref_set(v___y_3390_, v___x_3438_);
                v___x_3440_ =
                    l_Lean_compileDecl(v___x_3421_, v___x_3392_, v___y_3389_, v___y_3390_);
                if crate::leanh::lean_obj_tag(v___x_3440_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3440_, 1);
                    v___x_3441_ = lean_st_ref_get(v___y_3390_);
                    v_env_3442_ = crate::leanh::lean_ctor_get(v___x_3441_, 0);
                    crate::leanh::lean_inc_ref(v_env_3442_);
                    crate::leanh::lean_dec(v___x_3441_);
                    v___x_3443_ = l_Lean_Server_userRpcProcedures;
                    v___x_3444_ = l_Lean_MapDeclarationExtension_insert___redArg(
                        v___x_3443_,
                        v_env_3442_,
                        v_method_3380_,
                        v___x_3414_,
                    );
                    v___x_3445_ =
                        l_Lean_setEnv___at___00Lean_Server_registerRpcProcedure_spec__2___redArg(
                            v___x_3444_,
                            v___y_3390_,
                        );
                    return v___x_3445_;
                } else {
                    crate::leanh::lean_dec(v___x_3414_);
                    crate::leanh::lean_dec(v_method_3380_);
                    return v___x_3440_;
                }
            }
            6 => {
                if v_isShared_3455_ == 0 {
                    v___x_3457_ = v___x_3454_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
                    v___x_3457_ = v_reuseFailAlloc_3458_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3457_;
            }
            8 => {
                v___x_3469_ = l_Lean_Server_userRpcProcedures;
                crate::leanh::lean_inc(v_method_3380_);
                v___x_3470_ = l_Lean_MapDeclarationExtension_contains___redArg(
                    v___x_3460_,
                    v___x_3469_,
                    v_env_3387_,
                    v_method_3380_,
                );
                if v___x_3470_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3465_, 2);
                    v___y_3389_ = v___y_3467_;
                    v___y_3390_ = v___y_3468_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_method_3380_);
                    v___x_3471_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Server_registerRpcProcedure___closed__22),
                        core::ptr::addr_of_mut!(
                            l_Lean_Server_registerRpcProcedure___closed__22_once
                        ),
                        _init_l_Lean_Server_registerRpcProcedure___closed__22,
                    );
                    v___x_3472_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3472_, 0, v___x_3465_);
                    crate::leanh::lean_ctor_set(v___x_3472_, 1, v___x_3471_);
                    v___x_3473_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(v___x_3472_, v___y_3467_, v___y_3468_);
                    return v___x_3473_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_registerRpcProcedure___boxed(
    mut v_method_3478_: *mut crate::leanh::LeanObject,
    mut v_a_3479_: *mut crate::leanh::LeanObject,
    mut v_a_3480_: *mut crate::leanh::LeanObject,
    mut v_a_3481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3482_ = l_Lean_Server_registerRpcProcedure(v_method_3478_, v_a_3479_, v_a_3480_);
    crate::leanh::lean_dec(v_a_3480_);
    crate::leanh::lean_dec_ref(v_a_3479_);
    return v_res_3482_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(
    mut v_00_u03b1_3483_: *mut crate::leanh::LeanObject,
    mut v_msg_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3488_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(
        v_msg_3484_,
        v___y_3485_,
        v___y_3486_,
    );
    return v___x_3488_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___boxed(
    mut v_00_u03b1_3489_: *mut crate::leanh::LeanObject,
    mut v_msg_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3494_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3(
        v_00_u03b1_3489_,
        v_msg_3490_,
        v___y_3491_,
        v___y_3492_,
    );
    crate::leanh::lean_dec(v___y_3492_);
    crate::leanh::lean_dec_ref(v___y_3491_);
    return v_res_3494_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(
    mut v___x_3495_: *mut crate::leanh::LeanObject,
    mut v_decl_3496_: *mut crate::leanh::LeanObject,
    mut v_x_3497_: *mut crate::leanh::LeanObject,
    mut v_attrKind_3498_: u8,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_decl_3496_);
    v___x_3502_ = l_Lean_ensureAttrDeclIsMeta(
        v___x_3495_,
        v_decl_3496_,
        v_attrKind_3498_,
        v___y_3499_,
        v___y_3500_,
    );
    if crate::leanh::lean_obj_tag(v___x_3502_) == 0 {
        let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3502_, 1);
        v___x_3503_ = l_Lean_Server_registerRpcProcedure(v_decl_3496_, v___y_3499_, v___y_3500_);
        return v___x_3503_;
    } else {
        crate::leanh::lean_dec(v_decl_3496_);
        return v___x_3502_;
    }
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(
    mut v___x_3504_: *mut crate::leanh::LeanObject,
    mut v_decl_3505_: *mut crate::leanh::LeanObject,
    mut v_x_3506_: *mut crate::leanh::LeanObject,
    mut v_attrKind_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_3511_: u8 = 0;
    let mut v_res_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_3511_ = (crate::leanh::lean_unbox(v_attrKind_3507_) as u8);
    v_res_3512_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_3504_, v_decl_3505_, v_x_3506_, v_attrKind_boxed_3511_, v___y_3508_, v___y_3509_);
    crate::leanh::lean_dec(v___y_3509_);
    crate::leanh::lean_dec_ref(v___y_3508_);
    crate::leanh::lean_dec(v_x_3506_);
    return v_res_3512_;
}
pub unsafe fn _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3514_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__0_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_;
    v___x_3515_ = l_Lean_stringToMessageData(v___x_3514_);
    return v___x_3515_;
}
pub unsafe fn _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3517_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__2_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_;
    v___x_3518_ = l_Lean_stringToMessageData(v___x_3517_);
    return v___x_3518_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(
    mut v___x_3519_: *mut crate::leanh::LeanObject,
    mut v_decl_3520_: *mut crate::leanh::LeanObject,
    mut v___y_3521_: *mut crate::leanh::LeanObject,
    mut v___y_3522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3524_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
    v___x_3525_ = l_Lean_MessageData_ofName(v___x_3519_);
    v___x_3526_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3526_, 0, v___x_3524_);
    crate::leanh::lean_ctor_set(v___x_3526_, 1, v___x_3525_);
    v___x_3527_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1___closed__3_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_);
    v___x_3528_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3528_, 0, v___x_3526_);
    crate::leanh::lean_ctor_set(v___x_3528_, 1, v___x_3527_);
    v___x_3529_ = l_Lean_throwError___at___00Lean_Server_registerRpcProcedure_spec__3___redArg(
        v___x_3528_,
        v___y_3521_,
        v___y_3522_,
    );
    return v___x_3529_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(
    mut v___x_3530_: *mut crate::leanh::LeanObject,
    mut v_decl_3531_: *mut crate::leanh::LeanObject,
    mut v___y_3532_: *mut crate::leanh::LeanObject,
    mut v___y_3533_: *mut crate::leanh::LeanObject,
    mut v___y_3534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3535_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___lam__1_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_(v___x_3530_, v_decl_3531_, v___y_3532_, v___y_3533_);
    crate::leanh::lean_dec(v___y_3533_);
    crate::leanh::lean_dec_ref(v___y_3532_);
    crate::leanh::lean_dec(v_decl_3531_);
    return v_res_3535_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3615_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn___closed__31_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_;
    v___x_3616_ = l_Lean_registerBuiltinAttribute(v___x_3615_);
    return v___x_3616_;
}
pub unsafe fn l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2____boxed(
    mut v_a_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
    return v_res_3618_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Rpc_RequestHandling(
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
    res = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_475519820____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_builtinRpcProcedures,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_2946836025____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_userRpcProcedures = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Server_userRpcProcedures);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1370296685____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_RequestHandling_1988373275____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Rpc_RequestHandling(
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
pub unsafe fn initialize_Lean_Server_Rpc_RequestHandling(
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
    res = runtime_initialize_Lean_Server_Rpc_RequestHandling(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Rpc_RequestHandling(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Rpc_RequestHandling(builtin);
}
