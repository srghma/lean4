// Lean compiler output
// Module: Lean.Server.GoTo
// Imports: Lean.Server.Utils Lean.Data.Lsp.Internal Lean.Util.CollectFVars Lean.Util.ForEachExpr Lean.Parser.Module
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef, lean_erase_macro_scopes,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::AuxRecursor::{l_Lean_isAuxRecursor, l_Lean_isNoConfusion};
use crate::r#gen::Lean::Data::DeclarationRange::l_Lean_instInhabitedDeclarationRanges_default;
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::l_Lean_Json_getTag_x3f;
use crate::r#gen::Lean::Data::Lsp::Internal::{
    initialize_Lean_Data_Lsp_Internal, runtime_initialize_Lean_Data_Lsp_Internal,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_DeclarationRange_toLspRange;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::{l_Lean_builtinDeclRanges, l_Lean_declRangeExt};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_ContextInfo_runMetaM___redArg, l_Lean_Elab_Info_toElabInfo_x3f,
    l_Lean_Elab_InfoTree_findInfo_x3f,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_allImportedModuleNames, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::ErrorExplanation::l_Lean_errorExplanationExt;
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_constName_x3f,
    l_Lean_Expr_consumeMData, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppFn_x27,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar, l_Lean_Expr_hash, l_Lean_Expr_sort___override,
    l_Lean_instBEqFVarId_beq,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64,
};
use crate::r#gen::Lean::Meta::Instances::l_Lean_Meta_isInstance___redArg;
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_unfoldDefinition_x3f;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::MonadEnv::l_Lean_isRecCore;
use crate::r#gen::Lean::Parser::Module::{
    initialize_Lean_Parser_Module, runtime_initialize_Lean_Parser_Module,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ProjFns::l_Lean_Environment_getProjectionFnInfo_x3f;
use crate::r#gen::Lean::Server::InfoUtils::{l_Lean_Elab_Info_lctx, l_Lean_Elab_Info_range_x3f};
use crate::r#gen::Lean::Server::Utils::{
    initialize_Lean_Server_Utils, l_Lean_Server_documentUriFromModule_x3f,
    l_Lean_Syntax_Range_toLspRange, runtime_initialize_Lean_Server_Utils,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_getRange_x3f;
use crate::r#gen::Lean::Util::CollectFVars::{
    initialize_Lean_Util_CollectFVars, runtime_initialize_Lean_Util_CollectFVars,
};
use crate::r#gen::Lean::Util::ForEachExpr::{
    initialize_Lean_Util_ForEachExpr, runtime_initialize_Lean_Util_ForEachExpr,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Server_instBEqGoToKind___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Server_instBEqGoToKind_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Server_instBEqGoToKind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instBEqGoToKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instBEqGoToKind: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instBEqGoToKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__0_value:
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
    m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__2_value:
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
    m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__3_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__4_value:
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
    m_data: [116, 121, 112, 101, 0],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__5_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Server_instToJsonGoToKind_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Server_instToJsonGoToKind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instToJsonGoToKind: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0_value:
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
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111,
        117, 110, 100, 0,
    ],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Server_instFromJsonGoToKind_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instFromJsonGoToKind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_instFromJsonGoToKind: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_GoToKind_determineTargetExprs___closed__2_value:
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
    m_fun: l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_GoToKind_determineTargetExprs___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_GoToKind_determineTargetExprs___closed__3_value:
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
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_GoToKind_determineTargetExprs___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_getInstanceProjectionArg_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_getInstanceProjectionArg_x3f___closed__0: u64 = 0;
static mut l_Lean_Server_getInstanceProjectionArg_x3f___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_getInstanceProjectionArg_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_locationLinksFromDecl___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Server_locationLinksFromDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__0_value:
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
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__1_value:
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
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__2_value:
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
    m_data: [77, 111, 100, 117, 108, 101, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__3_value:
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
    m_data: [105, 109, 112, 111, 114, 116, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5561193377245250799 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3187861556840815537 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__7_value:
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
    m_data: [97, 108, 108, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5561193377245250799 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        9485984681193916779 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__9_value:
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
    m_data: [109, 101, 116, 97, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5561193377245250799 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        17003524124175295577 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__11_value:
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
    m_data: [112, 117, 98, 108, 105, 99, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5561193377245250799 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        12460543829726897862 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [68, 101, 108, 97, 98, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1_value) as *mut crate::leanh::LeanObject,15682102345768914502 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 108, 97, 98, 65, 112, 112, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5_value) as *mut crate::leanh::LeanObject,6086138408723263506 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7_value) as *mut crate::leanh::LeanObject,252081343774567219 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Server_GoToKind_ctorIdx(mut v_x_2784_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_2784_ {
        0 => {
            let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2785_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2785_;
        }
        1 => {
            let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2786_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2786_;
        }
        _ => {
            let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2787_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2787_;
        }
    }
}
pub unsafe fn l_Lean_Server_GoToKind_ctorIdx___boxed(
    mut v_x_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2789_: u8 = 0;
    let mut v_res_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2789_ = (crate::leanh::lean_unbox(v_x_2788_) as u8);
    v_res_2790_ = l_Lean_Server_GoToKind_ctorIdx(v_x_boxed_2789_);
    return v_res_2790_;
}
pub unsafe fn l_Lean_Server_GoToKind_toCtorIdx(mut v_x_2791_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2792_ = l_Lean_Server_GoToKind_ctorIdx(v_x_2791_);
    return v___x_2792_;
}
pub unsafe fn l_Lean_Server_GoToKind_toCtorIdx___boxed(
    mut v_x_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_2794_: u8 = 0;
    let mut v_res_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2794_ = (crate::leanh::lean_unbox(v_x_2793_) as u8);
    v_res_2795_ = l_Lean_Server_GoToKind_toCtorIdx(v_x_4__boxed_2794_);
    return v_res_2795_;
}
pub unsafe fn l_Lean_Server_GoToKind_ctorElim___redArg(
    mut v_k_2796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2796_);
    return v_k_2796_;
}
pub unsafe fn l_Lean_Server_GoToKind_ctorElim___redArg___boxed(
    mut v_k_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Lean_Server_GoToKind_ctorElim___redArg(v_k_2797_);
    crate::leanh::lean_dec(v_k_2797_);
    return v_res_2798_;
}
pub unsafe fn l_Lean_Server_GoToKind_ctorElim(
    mut v_motive_2799_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2800_: *mut crate::leanh::LeanObject,
    mut v_t_2801_: u8,
    mut v_h_2802_: *mut crate::leanh::LeanObject,
    mut v_k_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2803_);
    return v_k_2803_;
}
pub unsafe fn l_Lean_Server_GoToKind_ctorElim___boxed(
    mut v_motive_2804_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2805_: *mut crate::leanh::LeanObject,
    mut v_t_2806_: *mut crate::leanh::LeanObject,
    mut v_h_2807_: *mut crate::leanh::LeanObject,
    mut v_k_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2809_: u8 = 0;
    let mut v_res_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2809_ = (crate::leanh::lean_unbox(v_t_2806_) as u8);
    v_res_2810_ = l_Lean_Server_GoToKind_ctorElim(
        v_motive_2804_,
        v_ctorIdx_2805_,
        v_t_boxed_2809_,
        v_h_2807_,
        v_k_2808_,
    );
    crate::leanh::lean_dec(v_k_2808_);
    crate::leanh::lean_dec(v_ctorIdx_2805_);
    return v_res_2810_;
}
pub unsafe fn l_Lean_Server_GoToKind_declaration_elim___redArg(
    mut v_declaration_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_declaration_2811_);
    return v_declaration_2811_;
}
pub unsafe fn l_Lean_Server_GoToKind_declaration_elim___redArg___boxed(
    mut v_declaration_2812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2813_ = l_Lean_Server_GoToKind_declaration_elim___redArg(v_declaration_2812_);
    crate::leanh::lean_dec(v_declaration_2812_);
    return v_res_2813_;
}
pub unsafe fn l_Lean_Server_GoToKind_declaration_elim(
    mut v_motive_2814_: *mut crate::leanh::LeanObject,
    mut v_t_2815_: u8,
    mut v_h_2816_: *mut crate::leanh::LeanObject,
    mut v_declaration_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_declaration_2817_);
    return v_declaration_2817_;
}
pub unsafe fn l_Lean_Server_GoToKind_declaration_elim___boxed(
    mut v_motive_2818_: *mut crate::leanh::LeanObject,
    mut v_t_2819_: *mut crate::leanh::LeanObject,
    mut v_h_2820_: *mut crate::leanh::LeanObject,
    mut v_declaration_2821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2822_: u8 = 0;
    let mut v_res_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2822_ = (crate::leanh::lean_unbox(v_t_2819_) as u8);
    v_res_2823_ = l_Lean_Server_GoToKind_declaration_elim(
        v_motive_2818_,
        v_t_boxed_2822_,
        v_h_2820_,
        v_declaration_2821_,
    );
    crate::leanh::lean_dec(v_declaration_2821_);
    return v_res_2823_;
}
pub unsafe fn l_Lean_Server_GoToKind_definition_elim___redArg(
    mut v_definition_2824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_definition_2824_);
    return v_definition_2824_;
}
pub unsafe fn l_Lean_Server_GoToKind_definition_elim___redArg___boxed(
    mut v_definition_2825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2826_ = l_Lean_Server_GoToKind_definition_elim___redArg(v_definition_2825_);
    crate::leanh::lean_dec(v_definition_2825_);
    return v_res_2826_;
}
pub unsafe fn l_Lean_Server_GoToKind_definition_elim(
    mut v_motive_2827_: *mut crate::leanh::LeanObject,
    mut v_t_2828_: u8,
    mut v_h_2829_: *mut crate::leanh::LeanObject,
    mut v_definition_2830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_definition_2830_);
    return v_definition_2830_;
}
pub unsafe fn l_Lean_Server_GoToKind_definition_elim___boxed(
    mut v_motive_2831_: *mut crate::leanh::LeanObject,
    mut v_t_2832_: *mut crate::leanh::LeanObject,
    mut v_h_2833_: *mut crate::leanh::LeanObject,
    mut v_definition_2834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2835_: u8 = 0;
    let mut v_res_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2835_ = (crate::leanh::lean_unbox(v_t_2832_) as u8);
    v_res_2836_ = l_Lean_Server_GoToKind_definition_elim(
        v_motive_2831_,
        v_t_boxed_2835_,
        v_h_2833_,
        v_definition_2834_,
    );
    crate::leanh::lean_dec(v_definition_2834_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_Server_GoToKind_type_elim___redArg(
    mut v_type_2837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_type_2837_);
    return v_type_2837_;
}
pub unsafe fn l_Lean_Server_GoToKind_type_elim___redArg___boxed(
    mut v_type_2838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2839_ = l_Lean_Server_GoToKind_type_elim___redArg(v_type_2838_);
    crate::leanh::lean_dec(v_type_2838_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_Server_GoToKind_type_elim(
    mut v_motive_2840_: *mut crate::leanh::LeanObject,
    mut v_t_2841_: u8,
    mut v_h_2842_: *mut crate::leanh::LeanObject,
    mut v_type_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_type_2843_);
    return v_type_2843_;
}
pub unsafe fn l_Lean_Server_GoToKind_type_elim___boxed(
    mut v_motive_2844_: *mut crate::leanh::LeanObject,
    mut v_t_2845_: *mut crate::leanh::LeanObject,
    mut v_h_2846_: *mut crate::leanh::LeanObject,
    mut v_type_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2848_: u8 = 0;
    let mut v_res_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2848_ = (crate::leanh::lean_unbox(v_t_2845_) as u8);
    v_res_2849_ =
        l_Lean_Server_GoToKind_type_elim(v_motive_2844_, v_t_boxed_2848_, v_h_2846_, v_type_2847_);
    crate::leanh::lean_dec(v_type_2847_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Server_instBEqGoToKind_beq(mut v_x_2850_: u8, mut v_y_2851_: u8) -> u8 {
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u8 = 0;
    v___x_2852_ = l_Lean_Server_GoToKind_ctorIdx(v_x_2850_);
    v___x_2853_ = l_Lean_Server_GoToKind_ctorIdx(v_y_2851_);
    v___x_2854_ = lean_nat_dec_eq(v___x_2852_, v___x_2853_);
    crate::leanh::lean_dec(v___x_2853_);
    crate::leanh::lean_dec(v___x_2852_);
    return v___x_2854_;
}
pub unsafe fn l_Lean_Server_instBEqGoToKind_beq___boxed(
    mut v_x_2855_: *mut crate::leanh::LeanObject,
    mut v_y_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_2857_: u8 = 0;
    let mut v_y_18__boxed_2858_: u8 = 0;
    let mut v_res_2859_: u8 = 0;
    let mut v_r_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2857_ = (crate::leanh::lean_unbox(v_x_2855_) as u8);
    v_y_18__boxed_2858_ = (crate::leanh::lean_unbox(v_y_2856_) as u8);
    v_res_2859_ = l_Lean_Server_instBEqGoToKind_beq(v_x_17__boxed_2857_, v_y_18__boxed_2858_);
    v_r_2860_ = crate::leanh::lean_box((v_res_2859_) as usize);
    return v_r_2860_;
}
pub unsafe fn l_Lean_Server_instToJsonGoToKind_toJson(
    mut v_x_2872_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2872_ {
        0 => {
            let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2873_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__1;
            return v___x_2873_;
        }
        1 => {
            let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2874_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__3;
            return v___x_2874_;
        }
        _ => {
            let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2875_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__5;
            return v___x_2875_;
        }
    }
}
pub unsafe fn l_Lean_Server_instToJsonGoToKind_toJson___boxed(
    mut v_x_2876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_67__boxed_2877_: u8 = 0;
    let mut v_res_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_67__boxed_2877_ = (crate::leanh::lean_unbox(v_x_2876_) as u8);
    v_res_2878_ = l_Lean_Server_instToJsonGoToKind_toJson(v_x_67__boxed_2877_);
    return v_res_2878_;
}
pub unsafe fn l_Lean_Server_instFromJsonGoToKind_fromJson(
    mut v_json_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2897_ = l_Lean_Json_getTag_x3f(v_json_2896_);
    if crate::leanh::lean_obj_tag(v___x_2897_) == 0 {
        let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2898_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1;
        return v___x_2898_;
    } else {
        let mut v_val_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2901_: u8 = 0;
        v_val_2899_ = crate::leanh::lean_ctor_get(v___x_2897_, 0);
        crate::leanh::lean_inc(v_val_2899_);
        crate::leanh::lean_dec_ref_known(v___x_2897_, 1);
        v___x_2900_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__4;
        v___x_2901_ = lean_string_dec_eq(v_val_2899_, v___x_2900_);
        if v___x_2901_ == 0 {
            let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2903_: u8 = 0;
            v___x_2902_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__0;
            v___x_2903_ = lean_string_dec_eq(v_val_2899_, v___x_2902_);
            if v___x_2903_ == 0 {
                let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2905_: u8 = 0;
                v___x_2904_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__2;
                v___x_2905_ = lean_string_dec_eq(v_val_2899_, v___x_2904_);
                crate::leanh::lean_dec(v_val_2899_);
                if v___x_2905_ == 0 {
                    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2906_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3;
                    return v___x_2906_;
                } else {
                    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2907_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4;
                    return v___x_2907_;
                }
            } else {
                let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_val_2899_);
                v___x_2908_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5;
                return v___x_2908_;
            }
        } else {
            let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_2899_);
            v___x_2909_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6;
            return v___x_2909_;
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(
    mut v_e_2912_: *mut crate::leanh::LeanObject,
    mut v___y_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_unused_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2915_ = l_Lean_Expr_hasMVar(v_e_2912_);
                if v___x_2915_ == 0 {
                    v___x_2916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2916_, 0, v_e_2912_);
                    return v___x_2916_;
                } else {
                    v___x_2917_ = lean_st_ref_get(v___y_2913_);
                    v_mctx_2918_ = crate::leanh::lean_ctor_get(v___x_2917_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2918_);
                    crate::leanh::lean_dec(v___x_2917_);
                    v___x_2919_ = l_Lean_instantiateMVarsCore(v_mctx_2918_, v_e_2912_);
                    v_fst_2920_ = crate::leanh::lean_ctor_get(v___x_2919_, 0);
                    crate::leanh::lean_inc(v_fst_2920_);
                    v_snd_2921_ = crate::leanh::lean_ctor_get(v___x_2919_, 1);
                    crate::leanh::lean_inc(v_snd_2921_);
                    crate::leanh::lean_dec_ref(v___x_2919_);
                    v___x_2922_ = lean_st_ref_take(v___y_2913_);
                    v_cache_2923_ = crate::leanh::lean_ctor_get(v___x_2922_, 1);
                    v_zetaDeltaFVarIds_2924_ = crate::leanh::lean_ctor_get(v___x_2922_, 2);
                    v_postponed_2925_ = crate::leanh::lean_ctor_get(v___x_2922_, 3);
                    v_diag_2926_ = crate::leanh::lean_ctor_get(v___x_2922_, 4);
                    v_isSharedCheck_2935_ = (!crate::leanh::lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2935_ == 0 {
                        v_unused_2936_ = crate::leanh::lean_ctor_get(v___x_2922_, 0);
                        crate::leanh::lean_dec(v_unused_2936_);
                        v___x_2928_ = v___x_2922_;
                        v_isShared_2929_ = v_isSharedCheck_2935_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2926_);
                        crate::leanh::lean_inc(v_postponed_2925_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2924_);
                        crate::leanh::lean_inc(v_cache_2923_);
                        crate::leanh::lean_dec(v___x_2922_);
                        v___x_2928_ = crate::leanh::lean_box(0);
                        v_isShared_2929_ = v_isSharedCheck_2935_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2929_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2928_, 0, v_snd_2921_);
                    v___x_2931_ = v___x_2928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_snd_2921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_cache_2923_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2934_,
                        2,
                        v_zetaDeltaFVarIds_2924_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 3, v_postponed_2925_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 4, v_diag_2926_);
                    v___x_2931_ = v_reuseFailAlloc_2934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2932_ = lean_st_ref_set(v___y_2913_, v___x_2931_);
                v___x_2933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2933_, 0, v_fst_2920_);
                return v___x_2933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg___boxed(
    mut v_e_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ =
        l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(
            v_e_2937_,
            v___y_2938_,
        );
    crate::leanh::lean_dec(v___y_2938_);
    return v_res_2940_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(
    mut v_e_2941_: *mut crate::leanh::LeanObject,
    mut v___y_2942_: *mut crate::leanh::LeanObject,
    mut v___y_2943_: *mut crate::leanh::LeanObject,
    mut v___y_2944_: *mut crate::leanh::LeanObject,
    mut v___y_2945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ =
        l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(
            v_e_2941_,
            v___y_2943_,
        );
    return v___x_2947_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___boxed(
    mut v_e_2948_: *mut crate::leanh::LeanObject,
    mut v___y_2949_: *mut crate::leanh::LeanObject,
    mut v___y_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
    mut v___y_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2954_ =
        l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(
            v_e_2948_,
            v___y_2949_,
            v___y_2950_,
            v___y_2951_,
            v___y_2952_,
        );
    crate::leanh::lean_dec(v___y_2952_);
    crate::leanh::lean_dec_ref(v___y_2951_);
    crate::leanh::lean_dec(v___y_2950_);
    crate::leanh::lean_dec_ref(v___y_2949_);
    return v_res_2954_;
}
pub unsafe fn l_Lean_Server_GoToKind_determineTargetExprs___lam__0(
    mut v_e_2955_: *mut crate::leanh::LeanObject,
    mut v___y_2956_: *mut crate::leanh::LeanObject,
    mut v___y_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_2955_) {
                1 => {
                    v___x_2968_ = lean_array_push(v___y_2956_, v_e_2955_);
                    v_snd_2963_ = v___x_2968_;
                    state = 1;
                    continue;
                }
                4 => {
                    v___x_2969_ = lean_array_push(v___y_2956_, v_e_2955_);
                    v_snd_2963_ = v___x_2969_;
                    state = 1;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_2955_);
                    v_snd_2963_ = v___y_2956_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_2964_ = 1;
                v___x_2965_ = crate::leanh::lean_box((v___x_2964_) as usize);
                v___x_2966_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2966_, 0, v___x_2965_);
                crate::leanh::lean_ctor_set(v___x_2966_, 1, v_snd_2963_);
                v___x_2967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2967_, 0, v___x_2966_);
                return v___x_2967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed(
    mut v_e_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
    mut v___y_2974_: *mut crate::leanh::LeanObject,
    mut v___y_2975_: *mut crate::leanh::LeanObject,
    mut v___y_2976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2977_ = l_Lean_Server_GoToKind_determineTargetExprs___lam__0(
        v_e_2970_,
        v___y_2971_,
        v___y_2972_,
        v___y_2973_,
        v___y_2974_,
        v___y_2975_,
    );
    crate::leanh::lean_dec(v___y_2975_);
    crate::leanh::lean_dec_ref(v___y_2974_);
    crate::leanh::lean_dec(v___y_2973_);
    crate::leanh::lean_dec_ref(v___y_2972_);
    return v_res_2977_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(
    mut v_a_2978_: *mut crate::leanh::LeanObject,
    mut v_b_2979_: *mut crate::leanh::LeanObject,
    mut v_x_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2980_) == 0 {
                    crate::leanh::lean_dec(v_b_2979_);
                    crate::leanh::lean_dec_ref(v_a_2978_);
                    return v_x_2980_;
                } else {
                    v_key_2981_ = crate::leanh::lean_ctor_get(v_x_2980_, 0);
                    v_value_2982_ = crate::leanh::lean_ctor_get(v_x_2980_, 1);
                    v_tail_2983_ = crate::leanh::lean_ctor_get(v_x_2980_, 2);
                    v_isSharedCheck_2995_ = (!crate::leanh::lean_is_exclusive(v_x_2980_)) as u8;
                    if v_isSharedCheck_2995_ == 0 {
                        v___x_2985_ = v_x_2980_;
                        v_isShared_2986_ = v_isSharedCheck_2995_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2983_);
                        crate::leanh::lean_inc(v_value_2982_);
                        crate::leanh::lean_inc(v_key_2981_);
                        crate::leanh::lean_dec(v_x_2980_);
                        v___x_2985_ = crate::leanh::lean_box(0);
                        v_isShared_2986_ = v_isSharedCheck_2995_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2987_ = lean_expr_eqv(v_key_2981_, v_a_2978_);
                if v___x_2987_ == 0 {
                    v___x_2988_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_2978_, v_b_2979_, v_tail_2983_);
                    if v_isShared_2986_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2985_, 2, v___x_2988_);
                        v___x_2990_ = v___x_2985_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2991_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_key_2981_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_value_2982_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 2, v___x_2988_);
                        v___x_2990_ = v_reuseFailAlloc_2991_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2982_);
                    crate::leanh::lean_dec(v_key_2981_);
                    if v_isShared_2986_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2985_, 1, v_b_2979_);
                        crate::leanh::lean_ctor_set(v___x_2985_, 0, v_a_2978_);
                        v___x_2993_ = v___x_2985_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2994_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2978_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_b_2979_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_tail_2983_);
                        v___x_2993_ = v_reuseFailAlloc_2994_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2990_;
            }
            3 => {
                return v___x_2993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(
    mut v_a_2996_: *mut crate::leanh::LeanObject,
    mut v_x_2997_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2998_: u8 = 0;
    let mut v_key_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2997_) == 0 {
                    v___x_2998_ = 0;
                    return v___x_2998_;
                } else {
                    v_key_2999_ = crate::leanh::lean_ctor_get(v_x_2997_, 0);
                    v_tail_3000_ = crate::leanh::lean_ctor_get(v_x_2997_, 2);
                    v___x_3001_ = lean_expr_eqv(v_key_2999_, v_a_2996_);
                    if v___x_3001_ == 0 {
                        v_x_2997_ = v_tail_3000_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3001_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_a_3003_: *mut crate::leanh::LeanObject,
    mut v_x_3004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3005_: u8 = 0;
    let mut v_r_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3005_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_3003_, v_x_3004_);
    crate::leanh::lean_dec(v_x_3004_);
    crate::leanh::lean_dec_ref(v_a_3003_);
    v_r_3006_ = crate::leanh::lean_box((v_res_3005_) as usize);
    return v_r_3006_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(
    mut v_x_3007_: *mut crate::leanh::LeanObject,
    mut v_x_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3014_: u8 = 0;
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: u64 = 0;
    let mut v___x_3017_: u64 = 0;
    let mut v___x_3018_: u64 = 0;
    let mut v_fold_3019_: u64 = 0;
    let mut v___x_3020_: u64 = 0;
    let mut v___x_3021_: u64 = 0;
    let mut v___x_3022_: u64 = 0;
    let mut v___x_3023_: usize = 0;
    let mut v___x_3024_: usize = 0;
    let mut v___x_3025_: usize = 0;
    let mut v___x_3026_: usize = 0;
    let mut v___x_3027_: usize = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3008_) == 0 {
                    return v_x_3007_;
                } else {
                    v_key_3009_ = crate::leanh::lean_ctor_get(v_x_3008_, 0);
                    v_value_3010_ = crate::leanh::lean_ctor_get(v_x_3008_, 1);
                    v_tail_3011_ = crate::leanh::lean_ctor_get(v_x_3008_, 2);
                    v_isSharedCheck_3034_ = (!crate::leanh::lean_is_exclusive(v_x_3008_)) as u8;
                    if v_isSharedCheck_3034_ == 0 {
                        v___x_3013_ = v_x_3008_;
                        v_isShared_3014_ = v_isSharedCheck_3034_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3011_);
                        crate::leanh::lean_inc(v_value_3010_);
                        crate::leanh::lean_inc(v_key_3009_);
                        crate::leanh::lean_dec(v_x_3008_);
                        v___x_3013_ = crate::leanh::lean_box(0);
                        v_isShared_3014_ = v_isSharedCheck_3034_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3015_ = lean_array_get_size(v_x_3007_);
                v___x_3016_ = l_Lean_Expr_hash(v_key_3009_);
                v___x_3017_ = 32u64;
                v___x_3018_ = lean_uint64_shift_right(v___x_3016_, v___x_3017_);
                v_fold_3019_ = lean_uint64_xor(v___x_3016_, v___x_3018_);
                v___x_3020_ = 16u64;
                v___x_3021_ = lean_uint64_shift_right(v_fold_3019_, v___x_3020_);
                v___x_3022_ = lean_uint64_xor(v_fold_3019_, v___x_3021_);
                v___x_3023_ = lean_uint64_to_usize(v___x_3022_);
                v___x_3024_ = lean_usize_of_nat(v___x_3015_);
                v___x_3025_ = 1usize;
                v___x_3026_ = lean_usize_sub(v___x_3024_, v___x_3025_);
                v___x_3027_ = lean_usize_land(v___x_3023_, v___x_3026_);
                v___x_3028_ = lean_array_uget_borrowed(v_x_3007_, v___x_3027_);
                crate::leanh::lean_inc(v___x_3028_);
                if v_isShared_3014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3013_, 2, v___x_3028_);
                    v___x_3030_ = v___x_3013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_key_3009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_value_3010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 2, v___x_3028_);
                    v___x_3030_ = v_reuseFailAlloc_3033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3031_ = lean_array_uset(v_x_3007_, v___x_3027_, v___x_3030_);
                v_x_3007_ = v___x_3031_;
                v_x_3008_ = v_tail_3011_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(
    mut v_i_3035_: *mut crate::leanh::LeanObject,
    mut v_source_3036_: *mut crate::leanh::LeanObject,
    mut v_target_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v_es_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3038_ = lean_array_get_size(v_source_3036_);
                v___x_3039_ = lean_nat_dec_lt(v_i_3035_, v___x_3038_);
                if v___x_3039_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3036_);
                    crate::leanh::lean_dec(v_i_3035_);
                    return v_target_3037_;
                } else {
                    v_es_3040_ = lean_array_fget(v_source_3036_, v_i_3035_);
                    v___x_3041_ = crate::leanh::lean_box(0);
                    v_source_3042_ = lean_array_fset(v_source_3036_, v_i_3035_, v___x_3041_);
                    v_target_3043_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_target_3037_, v_es_3040_);
                    v___x_3044_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3045_ = lean_nat_add(v_i_3035_, v___x_3044_);
                    crate::leanh::lean_dec(v_i_3035_);
                    v_i_3035_ = v___x_3045_;
                    v_source_3036_ = v_source_3042_;
                    v_target_3037_ = v_target_3043_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(
    mut v_data_3047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = lean_array_get_size(v_data_3047_);
    v___x_3049_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3050_ = lean_nat_mul(v___x_3048_, v___x_3049_);
    v___x_3051_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3052_ = crate::leanh::lean_box(0);
    v___x_3053_ = lean_mk_array(v_nbuckets_3050_, v___x_3052_);
    v___x_3054_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v___x_3051_, v_data_3047_, v___x_3053_);
    return v___x_3054_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(
    mut v_m_3055_: *mut crate::leanh::LeanObject,
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v_b_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: u64 = 0;
    let mut v___x_3065_: u64 = 0;
    let mut v___x_3066_: u64 = 0;
    let mut v_fold_3067_: u64 = 0;
    let mut v___x_3068_: u64 = 0;
    let mut v___x_3069_: u64 = 0;
    let mut v___x_3070_: u64 = 0;
    let mut v___x_3071_: usize = 0;
    let mut v___x_3072_: usize = 0;
    let mut v___x_3073_: usize = 0;
    let mut v___x_3074_: usize = 0;
    let mut v___x_3075_: usize = 0;
    let mut v_bkt_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: u8 = 0;
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v_val_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3058_ = crate::leanh::lean_ctor_get(v_m_3055_, 0);
                v_buckets_3059_ = crate::leanh::lean_ctor_get(v_m_3055_, 1);
                v_isSharedCheck_3102_ = (!crate::leanh::lean_is_exclusive(v_m_3055_)) as u8;
                if v_isSharedCheck_3102_ == 0 {
                    v___x_3061_ = v_m_3055_;
                    v_isShared_3062_ = v_isSharedCheck_3102_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3059_);
                    crate::leanh::lean_inc(v_size_3058_);
                    crate::leanh::lean_dec(v_m_3055_);
                    v___x_3061_ = crate::leanh::lean_box(0);
                    v_isShared_3062_ = v_isSharedCheck_3102_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3063_ = lean_array_get_size(v_buckets_3059_);
                v___x_3064_ = l_Lean_Expr_hash(v_a_3056_);
                v___x_3065_ = 32u64;
                v___x_3066_ = lean_uint64_shift_right(v___x_3064_, v___x_3065_);
                v_fold_3067_ = lean_uint64_xor(v___x_3064_, v___x_3066_);
                v___x_3068_ = 16u64;
                v___x_3069_ = lean_uint64_shift_right(v_fold_3067_, v___x_3068_);
                v___x_3070_ = lean_uint64_xor(v_fold_3067_, v___x_3069_);
                v___x_3071_ = lean_uint64_to_usize(v___x_3070_);
                v___x_3072_ = lean_usize_of_nat(v___x_3063_);
                v___x_3073_ = 1usize;
                v___x_3074_ = lean_usize_sub(v___x_3072_, v___x_3073_);
                v___x_3075_ = lean_usize_land(v___x_3071_, v___x_3074_);
                v_bkt_3076_ = lean_array_uget_borrowed(v_buckets_3059_, v___x_3075_);
                v___x_3077_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_3056_, v_bkt_3076_);
                if v___x_3077_ == 0 {
                    v___x_3078_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3079_ = lean_nat_add(v_size_3058_, v___x_3078_);
                    crate::leanh::lean_dec(v_size_3058_);
                    crate::leanh::lean_inc(v_bkt_3076_);
                    v___x_3080_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3080_, 0, v_a_3056_);
                    crate::leanh::lean_ctor_set(v___x_3080_, 1, v_b_3057_);
                    crate::leanh::lean_ctor_set(v___x_3080_, 2, v_bkt_3076_);
                    v_buckets_x27_3081_ =
                        lean_array_uset(v_buckets_3059_, v___x_3075_, v___x_3080_);
                    v___x_3082_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3083_ = lean_nat_mul(v_size_x27_3079_, v___x_3082_);
                    v___x_3084_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3085_ = lean_nat_div(v___x_3083_, v___x_3084_);
                    crate::leanh::lean_dec(v___x_3083_);
                    v___x_3086_ = lean_array_get_size(v_buckets_x27_3081_);
                    v___x_3087_ = lean_nat_dec_le(v___x_3085_, v___x_3086_);
                    crate::leanh::lean_dec(v___x_3085_);
                    if v___x_3087_ == 0 {
                        v_val_3088_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_buckets_x27_3081_);
                        if v_isShared_3062_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3061_, 1, v_val_3088_);
                            crate::leanh::lean_ctor_set(v___x_3061_, 0, v_size_x27_3079_);
                            v___x_3090_ = v___x_3061_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3091_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3091_,
                                0,
                                v_size_x27_3079_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_val_3088_);
                            v___x_3090_ = v_reuseFailAlloc_3091_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3062_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3061_, 1, v_buckets_x27_3081_);
                            crate::leanh::lean_ctor_set(v___x_3061_, 0, v_size_x27_3079_);
                            v___x_3093_ = v___x_3061_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3094_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3094_,
                                0,
                                v_size_x27_3079_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3094_,
                                1,
                                v_buckets_x27_3081_,
                            );
                            v___x_3093_ = v_reuseFailAlloc_3094_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3076_);
                    v___x_3095_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3096_ =
                        lean_array_uset(v_buckets_3059_, v___x_3075_, v___x_3095_);
                    v___x_3097_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_3056_, v_b_3057_, v_bkt_3076_);
                    v___x_3098_ = lean_array_uset(v_buckets_x27_3096_, v___x_3075_, v___x_3097_);
                    if v_isShared_3062_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3061_, 1, v___x_3098_);
                        v___x_3100_ = v___x_3061_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3101_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_size_3058_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3098_);
                        v___x_3100_ = v_reuseFailAlloc_3101_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3090_;
            }
            3 => {
                return v___x_3093_;
            }
            4 => {
                return v___x_3100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(
    mut v_a_3103_: *mut crate::leanh::LeanObject,
    mut v_x_3104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3104_) == 0 {
                    v___x_3105_ = crate::leanh::lean_box(0);
                    return v___x_3105_;
                } else {
                    v_key_3106_ = crate::leanh::lean_ctor_get(v_x_3104_, 0);
                    v_value_3107_ = crate::leanh::lean_ctor_get(v_x_3104_, 1);
                    v_tail_3108_ = crate::leanh::lean_ctor_get(v_x_3104_, 2);
                    v___x_3109_ = lean_expr_eqv(v_key_3106_, v_a_3103_);
                    if v___x_3109_ == 0 {
                        v_x_3104_ = v_tail_3108_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3107_);
                        v___x_3111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3111_, 0, v_value_3107_);
                        return v___x_3111_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_a_3112_: *mut crate::leanh::LeanObject,
    mut v_x_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3114_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_3112_, v_x_3113_);
    crate::leanh::lean_dec(v_x_3113_);
    crate::leanh::lean_dec_ref(v_a_3112_);
    return v_res_3114_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(
    mut v_m_3115_: *mut crate::leanh::LeanObject,
    mut v_a_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: u64 = 0;
    let mut v___x_3120_: u64 = 0;
    let mut v___x_3121_: u64 = 0;
    let mut v_fold_3122_: u64 = 0;
    let mut v___x_3123_: u64 = 0;
    let mut v___x_3124_: u64 = 0;
    let mut v___x_3125_: u64 = 0;
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: usize = 0;
    let mut v___x_3128_: usize = 0;
    let mut v___x_3129_: usize = 0;
    let mut v___x_3130_: usize = 0;
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3117_ = crate::leanh::lean_ctor_get(v_m_3115_, 1);
    v___x_3118_ = lean_array_get_size(v_buckets_3117_);
    v___x_3119_ = l_Lean_Expr_hash(v_a_3116_);
    v___x_3120_ = 32u64;
    v___x_3121_ = lean_uint64_shift_right(v___x_3119_, v___x_3120_);
    v_fold_3122_ = lean_uint64_xor(v___x_3119_, v___x_3121_);
    v___x_3123_ = 16u64;
    v___x_3124_ = lean_uint64_shift_right(v_fold_3122_, v___x_3123_);
    v___x_3125_ = lean_uint64_xor(v_fold_3122_, v___x_3124_);
    v___x_3126_ = lean_uint64_to_usize(v___x_3125_);
    v___x_3127_ = lean_usize_of_nat(v___x_3118_);
    v___x_3128_ = 1usize;
    v___x_3129_ = lean_usize_sub(v___x_3127_, v___x_3128_);
    v___x_3130_ = lean_usize_land(v___x_3126_, v___x_3129_);
    v___x_3131_ = lean_array_uget_borrowed(v_buckets_3117_, v___x_3130_);
    v___x_3132_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_3116_, v___x_3131_);
    return v___x_3132_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg___boxed(
    mut v_m_3133_: *mut crate::leanh::LeanObject,
    mut v_a_3134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_3133_, v_a_3134_);
    crate::leanh::lean_dec_ref(v_a_3134_);
    crate::leanh::lean_dec_ref(v_m_3133_);
    return v_res_3135_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(
    mut v_g_3136_: *mut crate::leanh::LeanObject,
    mut v_e_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v_d_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3206_: u8 = 0;
    let mut v_a_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut v_val_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3156_ = lean_st_ref_get(v_a_3138_);
                v___x_3157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v___x_3156_, v_e_3137_);
                crate::leanh::lean_dec(v___x_3156_);
                if crate::leanh::lean_obj_tag(v___x_3157_) == 0 {
                    crate::leanh::lean_inc_ref(v_g_3136_);
                    crate::leanh::lean_inc(v___y_3143_);
                    crate::leanh::lean_inc_ref(v___y_3142_);
                    crate::leanh::lean_inc(v___y_3141_);
                    crate::leanh::lean_inc_ref(v___y_3140_);
                    crate::leanh::lean_inc_ref(v_e_3137_);
                    v___x_3158_ = crate::leanh::lean_apply_7(
                        v_g_3136_,
                        v_e_3137_,
                        v___y_3139_,
                        v___y_3140_,
                        v___y_3141_,
                        v___y_3142_,
                        v___y_3143_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3158_) == 0 {
                        v_a_3159_ = crate::leanh::lean_ctor_get(v___x_3158_, 0);
                        crate::leanh::lean_inc(v_a_3159_);
                        crate::leanh::lean_dec_ref_known(v___x_3158_, 1);
                        v_fst_3160_ = crate::leanh::lean_ctor_get(v_a_3159_, 0);
                        v_snd_3161_ = crate::leanh::lean_ctor_get(v_a_3159_, 1);
                        v_isSharedCheck_3206_ = (!crate::leanh::lean_is_exclusive(v_a_3159_)) as u8;
                        if v_isSharedCheck_3206_ == 0 {
                            v___x_3163_ = v_a_3159_;
                            v_isShared_3164_ = v_isSharedCheck_3206_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3161_);
                            crate::leanh::lean_inc(v_fst_3160_);
                            crate::leanh::lean_dec(v_a_3159_);
                            v___x_3163_ = crate::leanh::lean_box(0);
                            v_isShared_3164_ = v_isSharedCheck_3206_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3137_);
                        crate::leanh::lean_dec_ref(v_g_3136_);
                        v_a_3207_ = crate::leanh::lean_ctor_get(v___x_3158_, 0);
                        v_isSharedCheck_3214_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3158_)) as u8;
                        if v_isSharedCheck_3214_ == 0 {
                            v___x_3209_ = v___x_3158_;
                            v_isShared_3210_ = v_isSharedCheck_3214_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3207_);
                            crate::leanh::lean_dec(v___x_3158_);
                            v___x_3209_ = crate::leanh::lean_box(0);
                            v_isShared_3210_ = v_isSharedCheck_3214_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3137_);
                    crate::leanh::lean_dec_ref(v_g_3136_);
                    v_val_3215_ = crate::leanh::lean_ctor_get(v___x_3157_, 0);
                    v_isSharedCheck_3223_ = (!crate::leanh::lean_is_exclusive(v___x_3157_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3217_ = v___x_3157_;
                        v_isShared_3218_ = v_isSharedCheck_3223_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3215_);
                        crate::leanh::lean_dec(v___x_3157_);
                        v___x_3217_ = crate::leanh::lean_box(0);
                        v_isShared_3218_ = v_isSharedCheck_3223_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3148_ = lean_st_ref_take(v_a_3138_);
                v___x_3149_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v___x_3148_, v_e_3137_, v_fst_3147_);
                v___x_3150_ = lean_st_ref_set(v_a_3138_, v___x_3149_);
                v___x_3151_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3151_, 0, v_a_3146_);
                return v___x_3151_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3153_) == 0 {
                    v_a_3154_ = crate::leanh::lean_ctor_get(v___y_3153_, 0);
                    crate::leanh::lean_inc(v_a_3154_);
                    crate::leanh::lean_dec_ref_known(v___y_3153_, 1);
                    v_fst_3155_ = crate::leanh::lean_ctor_get(v_a_3154_, 0);
                    crate::leanh::lean_inc(v_fst_3155_);
                    v_a_3146_ = v_a_3154_;
                    v_fst_3147_ = v_fst_3155_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_3137_);
                    return v___y_3153_;
                }
            }
            3 => {
                v___x_3173_ = (crate::leanh::lean_unbox(v_fst_3160_) as u8);
                crate::leanh::lean_dec(v_fst_3160_);
                if v___x_3173_ == 0 {
                    crate::leanh::lean_dec_ref(v_g_3136_);
                    v___x_3174_ = crate::leanh::lean_box(0);
                    if v_isShared_3164_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3163_, 0, v___x_3174_);
                        v___x_3176_ = v___x_3163_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_snd_3161_);
                        v___x_3176_ = v_reuseFailAlloc_3177_;
                        state = 5;
                        continue;
                    }
                } else {
                    match crate::leanh::lean_obj_tag(v_e_3137_) {
                        7 => {
                            crate::leanh::lean_del_object(v___x_3163_);
                            v_binderType_3178_ = crate::leanh::lean_ctor_get(v_e_3137_, 1);
                            v_body_3179_ = crate::leanh::lean_ctor_get(v_e_3137_, 2);
                            crate::leanh::lean_inc_ref(v_body_3179_);
                            crate::leanh::lean_inc_ref(v_binderType_3178_);
                            v_d_3166_ = v_binderType_3178_;
                            v_b_3167_ = v_body_3179_;
                            v___y_3168_ = v_a_3138_;
                            state = 4;
                            continue;
                        }
                        6 => {
                            crate::leanh::lean_del_object(v___x_3163_);
                            v_binderType_3180_ = crate::leanh::lean_ctor_get(v_e_3137_, 1);
                            v_body_3181_ = crate::leanh::lean_ctor_get(v_e_3137_, 2);
                            crate::leanh::lean_inc_ref(v_body_3181_);
                            crate::leanh::lean_inc_ref(v_binderType_3180_);
                            v_d_3166_ = v_binderType_3180_;
                            v_b_3167_ = v_body_3181_;
                            v___y_3168_ = v_a_3138_;
                            state = 4;
                            continue;
                        }
                        8 => {
                            crate::leanh::lean_del_object(v___x_3163_);
                            v_type_3182_ = crate::leanh::lean_ctor_get(v_e_3137_, 1);
                            v_value_3183_ = crate::leanh::lean_ctor_get(v_e_3137_, 2);
                            v_body_3184_ = crate::leanh::lean_ctor_get(v_e_3137_, 3);
                            crate::leanh::lean_inc_ref(v_type_3182_);
                            crate::leanh::lean_inc_ref(v_g_3136_);
                            v___x_3185_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_type_3182_, v_a_3138_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                            if crate::leanh::lean_obj_tag(v___x_3185_) == 0 {
                                v_a_3186_ = crate::leanh::lean_ctor_get(v___x_3185_, 0);
                                crate::leanh::lean_inc(v_a_3186_);
                                crate::leanh::lean_dec_ref_known(v___x_3185_, 1);
                                v_snd_3187_ = crate::leanh::lean_ctor_get(v_a_3186_, 1);
                                crate::leanh::lean_inc(v_snd_3187_);
                                crate::leanh::lean_dec(v_a_3186_);
                                crate::leanh::lean_inc_ref(v_value_3183_);
                                crate::leanh::lean_inc_ref(v_g_3136_);
                                v___x_3188_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_value_3183_, v_a_3138_, v_snd_3187_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                                if crate::leanh::lean_obj_tag(v___x_3188_) == 0 {
                                    v_a_3189_ = crate::leanh::lean_ctor_get(v___x_3188_, 0);
                                    crate::leanh::lean_inc(v_a_3189_);
                                    crate::leanh::lean_dec_ref_known(v___x_3188_, 1);
                                    v_snd_3190_ = crate::leanh::lean_ctor_get(v_a_3189_, 1);
                                    crate::leanh::lean_inc(v_snd_3190_);
                                    crate::leanh::lean_dec(v_a_3189_);
                                    crate::leanh::lean_inc_ref(v_body_3184_);
                                    v___x_3191_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_body_3184_, v_a_3138_, v_snd_3190_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                                    v___y_3153_ = v___x_3191_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_g_3136_);
                                    v___y_3153_ = v___x_3188_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_g_3136_);
                                v___y_3153_ = v___x_3185_;
                                state = 2;
                                continue;
                            }
                        }
                        5 => {
                            crate::leanh::lean_del_object(v___x_3163_);
                            v_fn_3192_ = crate::leanh::lean_ctor_get(v_e_3137_, 0);
                            v_arg_3193_ = crate::leanh::lean_ctor_get(v_e_3137_, 1);
                            crate::leanh::lean_inc_ref(v_fn_3192_);
                            crate::leanh::lean_inc_ref(v_g_3136_);
                            v___x_3194_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_fn_3192_, v_a_3138_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                            if crate::leanh::lean_obj_tag(v___x_3194_) == 0 {
                                v_a_3195_ = crate::leanh::lean_ctor_get(v___x_3194_, 0);
                                crate::leanh::lean_inc(v_a_3195_);
                                crate::leanh::lean_dec_ref_known(v___x_3194_, 1);
                                v_snd_3196_ = crate::leanh::lean_ctor_get(v_a_3195_, 1);
                                crate::leanh::lean_inc(v_snd_3196_);
                                crate::leanh::lean_dec(v_a_3195_);
                                crate::leanh::lean_inc_ref(v_arg_3193_);
                                v___x_3197_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_arg_3193_, v_a_3138_, v_snd_3196_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                                v___y_3153_ = v___x_3197_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_g_3136_);
                                v___y_3153_ = v___x_3194_;
                                state = 2;
                                continue;
                            }
                        }
                        10 => {
                            crate::leanh::lean_del_object(v___x_3163_);
                            v_expr_3198_ = crate::leanh::lean_ctor_get(v_e_3137_, 1);
                            crate::leanh::lean_inc_ref(v_expr_3198_);
                            v___x_3199_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_expr_3198_, v_a_3138_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                            v___y_3153_ = v___x_3199_;
                            state = 2;
                            continue;
                        }
                        11 => {
                            crate::leanh::lean_del_object(v___x_3163_);
                            v_struct_3200_ = crate::leanh::lean_ctor_get(v_e_3137_, 2);
                            crate::leanh::lean_inc_ref(v_struct_3200_);
                            v___x_3201_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_struct_3200_, v_a_3138_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                            v___y_3153_ = v___x_3201_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_g_3136_);
                            v___x_3202_ = crate::leanh::lean_box(0);
                            if v_isShared_3164_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3163_, 0, v___x_3202_);
                                v___x_3204_ = v___x_3163_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3205_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_snd_3161_);
                                v___x_3204_ = v_reuseFailAlloc_3205_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_g_3136_);
                v___x_3169_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_d_3166_, v___y_3168_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                if crate::leanh::lean_obj_tag(v___x_3169_) == 0 {
                    v_a_3170_ = crate::leanh::lean_ctor_get(v___x_3169_, 0);
                    crate::leanh::lean_inc(v_a_3170_);
                    crate::leanh::lean_dec_ref_known(v___x_3169_, 1);
                    v_snd_3171_ = crate::leanh::lean_ctor_get(v_a_3170_, 1);
                    crate::leanh::lean_inc(v_snd_3171_);
                    crate::leanh::lean_dec(v_a_3170_);
                    v___x_3172_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_b_3167_, v___y_3168_, v_snd_3171_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                    v___y_3153_ = v___x_3172_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3167_);
                    crate::leanh::lean_dec_ref(v_g_3136_);
                    v___y_3153_ = v___x_3169_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v_a_3146_ = v___x_3176_;
                v_fst_3147_ = v___x_3174_;
                state = 1;
                continue;
            }
            6 => {
                v_a_3146_ = v___x_3204_;
                v_fst_3147_ = v___x_3202_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_3210_ == 0 {
                    v___x_3212_ = v___x_3209_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
                    v___x_3212_ = v_reuseFailAlloc_3213_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3212_;
            }
            9 => {
                v___x_3219_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3219_, 0, v_val_3215_);
                crate::leanh::lean_ctor_set(v___x_3219_, 1, v___y_3139_);
                if v_isShared_3218_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3217_, 0);
                    crate::leanh::lean_ctor_set(v___x_3217_, 0, v___x_3219_);
                    v___x_3221_ = v___x_3217_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
                    v___x_3221_ = v_reuseFailAlloc_3222_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1___boxed(
    mut v_g_3224_: *mut crate::leanh::LeanObject,
    mut v_e_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3233_ =
        l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(
            v_g_3224_,
            v_e_3225_,
            v_a_3226_,
            v___y_3227_,
            v___y_3228_,
            v___y_3229_,
            v___y_3230_,
            v___y_3231_,
        );
    crate::leanh::lean_dec(v___y_3231_);
    crate::leanh::lean_dec_ref(v___y_3230_);
    crate::leanh::lean_dec(v___y_3229_);
    crate::leanh::lean_dec_ref(v___y_3228_);
    crate::leanh::lean_dec(v_a_3226_);
    return v_res_3233_;
}
pub unsafe fn _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = crate::leanh::lean_box(0);
    v___x_3235_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3236_ = lean_mk_array(v___x_3235_, v___x_3234_);
    return v___x_3236_;
}
pub unsafe fn _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3237_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_GoToKind_determineTargetExprs___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Server_GoToKind_determineTargetExprs___closed__0_once),
        _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__0,
    );
    v___x_3238_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3239_, 0, v___x_3238_);
    crate::leanh::lean_ctor_set(v___x_3239_, 1, v___x_3237_);
    return v___x_3239_;
}
pub unsafe fn l_Lean_Server_GoToKind_determineTargetExprs(
    mut v_kind_3243_: u8,
    mut v_ti_3244_: *mut crate::leanh::LeanObject,
    mut v_a_3245_: *mut crate::leanh::LeanObject,
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_a_3247_: *mut crate::leanh::LeanObject,
    mut v_a_3248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expr_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3263_: u8 = 0;
    let mut v_snd_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3269_: u8 = 0;
    let mut v_a_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut v_a_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v_expr_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_kind_3243_ == 2 {
                    v_expr_3250_ = crate::leanh::lean_ctor_get(v_ti_3244_, 3);
                    crate::leanh::lean_inc_ref(v_expr_3250_);
                    crate::leanh::lean_dec_ref(v_ti_3244_);
                    crate::leanh::lean_inc(v_a_3248_);
                    crate::leanh::lean_inc_ref(v_a_3247_);
                    crate::leanh::lean_inc(v_a_3246_);
                    crate::leanh::lean_inc_ref(v_a_3245_);
                    v___x_3251_ =
                        lean_infer_type(v_expr_3250_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
                    if crate::leanh::lean_obj_tag(v___x_3251_) == 0 {
                        v_a_3252_ = crate::leanh::lean_ctor_get(v___x_3251_, 0);
                        crate::leanh::lean_inc(v_a_3252_);
                        crate::leanh::lean_dec_ref_known(v___x_3251_, 1);
                        v___x_3253_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_a_3252_, v_a_3246_);
                        v_a_3254_ = crate::leanh::lean_ctor_get(v___x_3253_, 0);
                        crate::leanh::lean_inc(v_a_3254_);
                        crate::leanh::lean_dec_ref(v___x_3253_);
                        v___x_3255_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Server_GoToKind_determineTargetExprs___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Server_GoToKind_determineTargetExprs___closed__1_once
                            ),
                            _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1,
                        );
                        v___x_3256_ = lean_st_mk_ref(v___x_3255_);
                        v___f_3257_ = l_Lean_Server_GoToKind_determineTargetExprs___closed__2;
                        v___x_3258_ = l_Lean_Server_GoToKind_determineTargetExprs___closed__3;
                        v___x_3259_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v___f_3257_, v_a_3254_, v___x_3256_, v___x_3258_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
                        if crate::leanh::lean_obj_tag(v___x_3259_) == 0 {
                            v_a_3260_ = crate::leanh::lean_ctor_get(v___x_3259_, 0);
                            v_isSharedCheck_3269_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3259_)) as u8;
                            if v_isSharedCheck_3269_ == 0 {
                                v___x_3262_ = v___x_3259_;
                                v_isShared_3263_ = v_isSharedCheck_3269_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3260_);
                                crate::leanh::lean_dec(v___x_3259_);
                                v___x_3262_ = crate::leanh::lean_box(0);
                                v_isShared_3263_ = v_isSharedCheck_3269_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3256_);
                            v_a_3270_ = crate::leanh::lean_ctor_get(v___x_3259_, 0);
                            v_isSharedCheck_3277_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3259_)) as u8;
                            if v_isSharedCheck_3277_ == 0 {
                                v___x_3272_ = v___x_3259_;
                                v_isShared_3273_ = v_isSharedCheck_3277_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3270_);
                                crate::leanh::lean_dec(v___x_3259_);
                                v___x_3272_ = crate::leanh::lean_box(0);
                                v_isShared_3273_ = v_isSharedCheck_3277_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_3278_ = crate::leanh::lean_ctor_get(v___x_3251_, 0);
                        v_isSharedCheck_3285_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3251_)) as u8;
                        if v_isSharedCheck_3285_ == 0 {
                            v___x_3280_ = v___x_3251_;
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3278_);
                            crate::leanh::lean_dec(v___x_3251_);
                            v___x_3280_ = crate::leanh::lean_box(0);
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_expr_3286_ = crate::leanh::lean_ctor_get(v_ti_3244_, 3);
                    crate::leanh::lean_inc_ref(v_expr_3286_);
                    crate::leanh::lean_dec_ref(v_ti_3244_);
                    v___x_3287_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_3286_, v_a_3246_);
                    v_a_3288_ = crate::leanh::lean_ctor_get(v___x_3287_, 0);
                    v_isSharedCheck_3298_ = (!crate::leanh::lean_is_exclusive(v___x_3287_)) as u8;
                    if v_isSharedCheck_3298_ == 0 {
                        v___x_3290_ = v___x_3287_;
                        v_isShared_3291_ = v_isSharedCheck_3298_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3288_);
                        crate::leanh::lean_dec(v___x_3287_);
                        v___x_3290_ = crate::leanh::lean_box(0);
                        v_isShared_3291_ = v_isSharedCheck_3298_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3264_ = crate::leanh::lean_ctor_get(v_a_3260_, 1);
                crate::leanh::lean_inc(v_snd_3264_);
                crate::leanh::lean_dec(v_a_3260_);
                v___x_3265_ = lean_st_ref_get(v___x_3256_);
                crate::leanh::lean_dec(v___x_3256_);
                crate::leanh::lean_dec(v___x_3265_);
                if v_isShared_3263_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3262_, 0, v_snd_3264_);
                    v___x_3267_ = v___x_3262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_snd_3264_);
                    v___x_3267_ = v_reuseFailAlloc_3268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3267_;
            }
            3 => {
                if v_isShared_3273_ == 0 {
                    v___x_3275_ = v___x_3272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3276_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
                    v___x_3275_ = v_reuseFailAlloc_3276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3275_;
            }
            5 => {
                if v_isShared_3281_ == 0 {
                    v___x_3283_ = v___x_3280_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
                    v___x_3283_ = v_reuseFailAlloc_3284_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3283_;
            }
            7 => {
                v___x_3292_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3293_ = lean_mk_empty_array_with_capacity(v___x_3292_);
                v___x_3294_ = lean_array_push(v___x_3293_, v_a_3288_);
                if v_isShared_3291_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3290_, 0, v___x_3294_);
                    v___x_3296_ = v___x_3290_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
                    v___x_3296_ = v_reuseFailAlloc_3297_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_GoToKind_determineTargetExprs___boxed(
    mut v_kind_3299_: *mut crate::leanh::LeanObject,
    mut v_ti_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_3306_: u8 = 0;
    let mut v_res_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3306_ = (crate::leanh::lean_unbox(v_kind_3299_) as u8);
    v_res_3307_ = l_Lean_Server_GoToKind_determineTargetExprs(
        v_kind_boxed_3306_,
        v_ti_3300_,
        v_a_3301_,
        v_a_3302_,
        v_a_3303_,
        v_a_3304_,
    );
    crate::leanh::lean_dec(v_a_3304_);
    crate::leanh::lean_dec_ref(v_a_3303_);
    crate::leanh::lean_dec(v_a_3302_);
    crate::leanh::lean_dec_ref(v_a_3301_);
    return v_res_3307_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(
    mut v_00_u03b2_3308_: *mut crate::leanh::LeanObject,
    mut v_m_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_3309_, v_a_3310_);
    return v___x_3311_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___boxed(
    mut v_00_u03b2_3312_: *mut crate::leanh::LeanObject,
    mut v_m_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(v_00_u03b2_3312_, v_m_3313_, v_a_3314_);
    crate::leanh::lean_dec_ref(v_a_3314_);
    crate::leanh::lean_dec_ref(v_m_3313_);
    return v_res_3315_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2(
    mut v_00_u03b2_3316_: *mut crate::leanh::LeanObject,
    mut v_m_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
    mut v_b_3319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v_m_3317_, v_a_3318_, v_b_3319_);
    return v___x_3320_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(
    mut v_00_u03b2_3321_: *mut crate::leanh::LeanObject,
    mut v_a_3322_: *mut crate::leanh::LeanObject,
    mut v_x_3323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_3322_, v_x_3323_);
    return v___x_3324_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_3325_: *mut crate::leanh::LeanObject,
    mut v_a_3326_: *mut crate::leanh::LeanObject,
    mut v_x_3327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(v_00_u03b2_3325_, v_a_3326_, v_x_3327_);
    crate::leanh::lean_dec(v_x_3327_);
    crate::leanh::lean_dec_ref(v_a_3326_);
    return v_res_3328_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3329_: *mut crate::leanh::LeanObject,
    mut v_a_3330_: *mut crate::leanh::LeanObject,
    mut v_x_3331_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3332_: u8 = 0;
    v___x_3332_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_3330_, v_x_3331_);
    return v___x_3332_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_x_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3336_: u8 = 0;
    let mut v_r_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(v_00_u03b2_3333_, v_a_3334_, v_x_3335_);
    crate::leanh::lean_dec(v_x_3335_);
    crate::leanh::lean_dec_ref(v_a_3334_);
    v_r_3337_ = crate::leanh::lean_box((v_res_3336_) as usize);
    return v_r_3337_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5(
    mut v_00_u03b2_3338_: *mut crate::leanh::LeanObject,
    mut v_data_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3340_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_data_3339_);
    return v___x_3340_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6(
    mut v_00_u03b2_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_b_3343_: *mut crate::leanh::LeanObject,
    mut v_x_3344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_3342_, v_b_3343_, v_x_3344_);
    return v___x_3345_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6(
    mut v_00_u03b2_3346_: *mut crate::leanh::LeanObject,
    mut v_i_3347_: *mut crate::leanh::LeanObject,
    mut v_source_3348_: *mut crate::leanh::LeanObject,
    mut v_target_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3350_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v_i_3347_, v_source_3348_, v_target_3349_);
    return v___x_3350_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7(
    mut v_00_u03b2_3351_: *mut crate::leanh::LeanObject,
    mut v_x_3352_: *mut crate::leanh::LeanObject,
    mut v_x_3353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_x_3352_, v_x_3353_);
    return v___x_3354_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(
    mut v_e_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_a_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut v___x_3376_: u8 = 0;
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3381_: u8 = 0;
    let mut v_val_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3388_: u8 = 0;
    let mut v_a_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3392_: u8 = 0;
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3361_ = lean_st_ref_get(v_a_3359_);
                v___x_3362_ = l_Lean_Expr_getAppFn_x27(v_e_3355_);
                if crate::leanh::lean_obj_tag(v___x_3362_) == 4 {
                    v_declName_3363_ = crate::leanh::lean_ctor_get(v___x_3362_, 0);
                    crate::leanh::lean_inc(v_declName_3363_);
                    crate::leanh::lean_dec_ref_known(v___x_3362_, 2);
                    v_env_3364_ = crate::leanh::lean_ctor_get(v___x_3361_, 0);
                    crate::leanh::lean_inc_ref(v_env_3364_);
                    crate::leanh::lean_dec(v___x_3361_);
                    v___x_3365_ =
                        l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3364_, v_declName_3363_);
                    if crate::leanh::lean_obj_tag(v___x_3365_) == 1 {
                        v_val_3366_ = crate::leanh::lean_ctor_get(v___x_3365_, 0);
                        v_isSharedCheck_3375_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3365_)) as u8;
                        if v_isSharedCheck_3375_ == 0 {
                            v___x_3368_ = v___x_3365_;
                            v_isShared_3369_ = v_isSharedCheck_3375_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3366_);
                            crate::leanh::lean_dec(v___x_3365_);
                            v___x_3368_ = crate::leanh::lean_box(0);
                            v_isShared_3369_ = v_isSharedCheck_3375_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3365_);
                        v___x_3376_ = 0;
                        v___x_3377_ = l_Lean_Meta_unfoldDefinition_x3f(
                            v_e_3355_,
                            v___x_3376_,
                            v_a_3356_,
                            v_a_3357_,
                            v_a_3358_,
                            v_a_3359_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3377_) == 0 {
                            v_a_3378_ = crate::leanh::lean_ctor_get(v___x_3377_, 0);
                            v_isSharedCheck_3388_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3377_)) as u8;
                            if v_isSharedCheck_3388_ == 0 {
                                v___x_3380_ = v___x_3377_;
                                v_isShared_3381_ = v_isSharedCheck_3388_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3378_);
                                crate::leanh::lean_dec(v___x_3377_);
                                v___x_3380_ = crate::leanh::lean_box(0);
                                v_isShared_3381_ = v_isSharedCheck_3388_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_3389_ = crate::leanh::lean_ctor_get(v___x_3377_, 0);
                            v_isSharedCheck_3396_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3377_)) as u8;
                            if v_isSharedCheck_3396_ == 0 {
                                v___x_3391_ = v___x_3377_;
                                v_isShared_3392_ = v_isSharedCheck_3396_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3389_);
                                crate::leanh::lean_dec(v___x_3377_);
                                v___x_3391_ = crate::leanh::lean_box(0);
                                v_isShared_3392_ = v_isSharedCheck_3396_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3362_);
                    crate::leanh::lean_dec(v___x_3361_);
                    crate::leanh::lean_dec_ref(v_e_3355_);
                    v___x_3397_ = crate::leanh::lean_box(0);
                    v___x_3398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3398_, 0, v___x_3397_);
                    return v___x_3398_;
                }
            }
            1 => {
                v___x_3370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3370_, 0, v_e_3355_);
                crate::leanh::lean_ctor_set(v___x_3370_, 1, v_val_3366_);
                if v_isShared_3369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3368_, 0, v___x_3370_);
                    v___x_3372_ = v___x_3368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3374_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3370_);
                    v___x_3372_ = v_reuseFailAlloc_3374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3373_, 0, v___x_3372_);
                return v___x_3373_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_3378_) == 1 {
                    crate::leanh::lean_del_object(v___x_3380_);
                    v_val_3382_ = crate::leanh::lean_ctor_get(v_a_3378_, 0);
                    crate::leanh::lean_inc(v_val_3382_);
                    crate::leanh::lean_dec_ref_known(v_a_3378_, 1);
                    v_e_3355_ = v_val_3382_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3378_);
                    v___x_3384_ = crate::leanh::lean_box(0);
                    if v_isShared_3381_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3380_, 0, v___x_3384_);
                        v___x_3386_ = v___x_3380_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
                        v___x_3386_ = v_reuseFailAlloc_3387_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3386_;
            }
            5 => {
                if v_isShared_3392_ == 0 {
                    v___x_3394_ = v___x_3391_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
                    v___x_3394_ = v_reuseFailAlloc_3395_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f___boxed(
    mut v_e_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
    mut v_a_3401_: *mut crate::leanh::LeanObject,
    mut v_a_3402_: *mut crate::leanh::LeanObject,
    mut v_a_3403_: *mut crate::leanh::LeanObject,
    mut v_a_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3405_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
    crate::leanh::lean_dec(v_a_3403_);
    crate::leanh::lean_dec_ref(v_a_3402_);
    crate::leanh::lean_dec(v_a_3401_);
    crate::leanh::lean_dec_ref(v_a_3400_);
    return v_res_3405_;
}
pub unsafe fn _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0() -> u64 {
    let mut v___x_3406_: u8 = 0;
    let mut v___x_3407_: u64 = 0;
    v___x_3406_ = 2;
    v___x_3407_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3406_);
    return v___x_3407_;
}
pub unsafe fn _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3408_ = crate::leanh::lean_box(0);
    v_dummy_3409_ = l_Lean_Expr_sort___override(v___x_3408_);
    return v_dummy_3409_;
}
pub unsafe fn l_Lean_Server_getInstanceProjectionArg_x3f(
    mut v_e_3410_: *mut crate::leanh::LeanObject,
    mut v_a_3411_: *mut crate::leanh::LeanObject,
    mut v_a_3412_: *mut crate::leanh::LeanObject,
    mut v_a_3413_: *mut crate::leanh::LeanObject,
    mut v_a_3414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3417_: u8 = 0;
    let mut v_ctxApprox_3418_: u8 = 0;
    let mut v_quasiPatternApprox_3419_: u8 = 0;
    let mut v_constApprox_3420_: u8 = 0;
    let mut v_isDefEqStuckEx_3421_: u8 = 0;
    let mut v_unificationHints_3422_: u8 = 0;
    let mut v_proofIrrelevance_3423_: u8 = 0;
    let mut v_assignSyntheticOpaque_3424_: u8 = 0;
    let mut v_offsetCnstrs_3425_: u8 = 0;
    let mut v_etaStruct_3426_: u8 = 0;
    let mut v_univApprox_3427_: u8 = 0;
    let mut v_iota_3428_: u8 = 0;
    let mut v_beta_3429_: u8 = 0;
    let mut v_proj_3430_: u8 = 0;
    let mut v_zeta_3431_: u8 = 0;
    let mut v_zetaDelta_3432_: u8 = 0;
    let mut v_zetaUnused_3433_: u8 = 0;
    let mut v_zetaHave_3434_: u8 = 0;
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3437_: u8 = 0;
    let mut v_trackZetaDelta_3438_: u8 = 0;
    let mut v_zetaDeltaSet_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3445_: u8 = 0;
    let mut v_inTypeClassResolution_3446_: u8 = 0;
    let mut v_cacheInferType_3447_: u8 = 0;
    let mut v___x_3448_: u8 = 0;
    let mut v_config_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: u64 = 0;
    let mut v___x_3452_: u64 = 0;
    let mut v___x_3453_: u64 = 0;
    let mut v___x_3454_: u64 = 0;
    let mut v___x_3455_: u64 = 0;
    let mut v_key_3456_: u64 = 0;
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3463_: u8 = 0;
    let mut v_val_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v_snd_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3490_: u8 = 0;
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut v_a_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3499_: u8 = 0;
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3503_: u8 = 0;
    let mut v_reuseFailAlloc_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3416_ = l_Lean_Meta_Context_config(v_a_3411_);
                v_foApprox_3417_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 0 as u32);
                v_ctxApprox_3418_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 1 as u32);
                v_quasiPatternApprox_3419_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_3416_, 2 as u32);
                v_constApprox_3420_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 3 as u32);
                v_isDefEqStuckEx_3421_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 4 as u32);
                v_unificationHints_3422_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 5 as u32);
                v_proofIrrelevance_3423_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 6 as u32);
                v_assignSyntheticOpaque_3424_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_3416_, 7 as u32);
                v_offsetCnstrs_3425_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 8 as u32);
                v_etaStruct_3426_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 10 as u32);
                v_univApprox_3427_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 11 as u32);
                v_iota_3428_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 12 as u32);
                v_beta_3429_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 13 as u32);
                v_proj_3430_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 14 as u32);
                v_zeta_3431_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 15 as u32);
                v_zetaDelta_3432_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 16 as u32);
                v_zetaUnused_3433_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 17 as u32);
                v_zetaHave_3434_ = crate::leanh::lean_ctor_get_uint8(v___x_3416_, 18 as u32);
                v_isSharedCheck_3505_ = (!crate::leanh::lean_is_exclusive(v___x_3416_)) as u8;
                if v_isSharedCheck_3505_ == 0 {
                    v___x_3436_ = v___x_3416_;
                    v_isShared_3437_ = v_isSharedCheck_3505_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3416_);
                    v___x_3436_ = crate::leanh::lean_box(0);
                    v_isShared_3437_ = v_isSharedCheck_3505_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_3438_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3411_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3439_ = crate::leanh::lean_ctor_get(v_a_3411_, 1);
                v_lctx_3440_ = crate::leanh::lean_ctor_get(v_a_3411_, 2);
                v_localInstances_3441_ = crate::leanh::lean_ctor_get(v_a_3411_, 3);
                v_defEqCtx_x3f_3442_ = crate::leanh::lean_ctor_get(v_a_3411_, 4);
                v_synthPendingDepth_3443_ = crate::leanh::lean_ctor_get(v_a_3411_, 5);
                v_canUnfold_x3f_3444_ = crate::leanh::lean_ctor_get(v_a_3411_, 6);
                v_univApprox_3445_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3411_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3446_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3411_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3447_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3411_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3448_ = 2;
                if v_isShared_3437_ == 0 {
                    v_config_3450_ = v___x_3436_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3504_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        0 as u32,
                        v_foApprox_3417_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        1 as u32,
                        v_ctxApprox_3418_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        2 as u32,
                        v_quasiPatternApprox_3419_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        3 as u32,
                        v_constApprox_3420_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        4 as u32,
                        v_isDefEqStuckEx_3421_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        5 as u32,
                        v_unificationHints_3422_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        6 as u32,
                        v_proofIrrelevance_3423_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        7 as u32,
                        v_assignSyntheticOpaque_3424_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        8 as u32,
                        v_offsetCnstrs_3425_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        10 as u32,
                        v_etaStruct_3426_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        11 as u32,
                        v_univApprox_3427_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        12 as u32,
                        v_iota_3428_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        13 as u32,
                        v_beta_3429_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        14 as u32,
                        v_proj_3430_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        15 as u32,
                        v_zeta_3431_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        16 as u32,
                        v_zetaDelta_3432_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        17 as u32,
                        v_zetaUnused_3433_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        18 as u32,
                        v_zetaHave_3434_,
                    );
                    v_config_3450_ = v_reuseFailAlloc_3504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_3450_, 9 as u32, v___x_3448_);
                v___x_3451_ = l_Lean_Meta_Context_configKey(v_a_3411_);
                v___x_3452_ = 3u64;
                v___x_3453_ = lean_uint64_shift_right(v___x_3451_, v___x_3452_);
                v___x_3454_ = lean_uint64_shift_left(v___x_3453_, v___x_3452_);
                v___x_3455_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_getInstanceProjectionArg_x3f___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_getInstanceProjectionArg_x3f___closed__0_once
                    ),
                    _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0,
                );
                v_key_3456_ = lean_uint64_lor(v___x_3454_, v___x_3455_);
                v___x_3457_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_3457_, 0, v_config_3450_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_3457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_3456_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_3444_);
                crate::leanh::lean_inc(v_synthPendingDepth_3443_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_3442_);
                crate::leanh::lean_inc_ref(v_localInstances_3441_);
                crate::leanh::lean_inc_ref(v_lctx_3440_);
                crate::leanh::lean_inc(v_zetaDeltaSet_3439_);
                v___x_3458_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_3458_, 0, v___x_3457_);
                crate::leanh::lean_ctor_set(v___x_3458_, 1, v_zetaDeltaSet_3439_);
                crate::leanh::lean_ctor_set(v___x_3458_, 2, v_lctx_3440_);
                crate::leanh::lean_ctor_set(v___x_3458_, 3, v_localInstances_3441_);
                crate::leanh::lean_ctor_set(v___x_3458_, 4, v_defEqCtx_x3f_3442_);
                crate::leanh::lean_ctor_set(v___x_3458_, 5, v_synthPendingDepth_3443_);
                crate::leanh::lean_ctor_set(v___x_3458_, 6, v_canUnfold_x3f_3444_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3438_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3445_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3446_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3447_,
                );
                v___x_3459_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_3410_, v___x_3458_, v_a_3412_, v_a_3413_, v_a_3414_);
                crate::leanh::lean_dec_ref_known(v___x_3458_, 7);
                if crate::leanh::lean_obj_tag(v___x_3459_) == 0 {
                    v_a_3460_ = crate::leanh::lean_ctor_get(v___x_3459_, 0);
                    v_isSharedCheck_3495_ = (!crate::leanh::lean_is_exclusive(v___x_3459_)) as u8;
                    if v_isSharedCheck_3495_ == 0 {
                        v___x_3462_ = v___x_3459_;
                        v_isShared_3463_ = v_isSharedCheck_3495_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3460_);
                        crate::leanh::lean_dec(v___x_3459_);
                        v___x_3462_ = crate::leanh::lean_box(0);
                        v_isShared_3463_ = v_isSharedCheck_3495_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_3496_ = crate::leanh::lean_ctor_get(v___x_3459_, 0);
                    v_isSharedCheck_3503_ = (!crate::leanh::lean_is_exclusive(v___x_3459_)) as u8;
                    if v_isSharedCheck_3503_ == 0 {
                        v___x_3498_ = v___x_3459_;
                        v_isShared_3499_ = v_isSharedCheck_3503_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3496_);
                        crate::leanh::lean_dec(v___x_3459_);
                        v___x_3498_ = crate::leanh::lean_box(0);
                        v_isShared_3499_ = v_isSharedCheck_3503_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_3460_) == 1 {
                    v_val_3464_ = crate::leanh::lean_ctor_get(v_a_3460_, 0);
                    v_isSharedCheck_3490_ = (!crate::leanh::lean_is_exclusive(v_a_3460_)) as u8;
                    if v_isSharedCheck_3490_ == 0 {
                        v___x_3466_ = v_a_3460_;
                        v_isShared_3467_ = v_isSharedCheck_3490_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3464_);
                        crate::leanh::lean_dec(v_a_3460_);
                        v___x_3466_ = crate::leanh::lean_box(0);
                        v_isShared_3467_ = v_isSharedCheck_3490_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3460_);
                    v___x_3491_ = crate::leanh::lean_box(0);
                    if v_isShared_3463_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3462_, 0, v___x_3491_);
                        v___x_3493_ = v___x_3462_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
                        v___x_3493_ = v_reuseFailAlloc_3494_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_snd_3468_ = crate::leanh::lean_ctor_get(v_val_3464_, 1);
                crate::leanh::lean_inc(v_snd_3468_);
                v_fst_3469_ = crate::leanh::lean_ctor_get(v_val_3464_, 0);
                crate::leanh::lean_inc(v_fst_3469_);
                crate::leanh::lean_dec(v_val_3464_);
                v_numParams_3470_ = crate::leanh::lean_ctor_get(v_snd_3468_, 1);
                crate::leanh::lean_inc(v_numParams_3470_);
                crate::leanh::lean_dec(v_snd_3468_);
                v_dummy_3471_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_getInstanceProjectionArg_x3f___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_getInstanceProjectionArg_x3f___closed__1_once
                    ),
                    _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__1,
                );
                v_nargs_3472_ = l_Lean_Expr_getAppNumArgs(v_fst_3469_);
                crate::leanh::lean_inc(v_nargs_3472_);
                v___x_3473_ = lean_mk_array(v_nargs_3472_, v_dummy_3471_);
                v___x_3474_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3475_ = lean_nat_sub(v_nargs_3472_, v___x_3474_);
                crate::leanh::lean_dec(v_nargs_3472_);
                v___x_3476_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_fst_3469_,
                    v___x_3473_,
                    v___x_3475_,
                );
                v___x_3477_ = lean_array_get_size(v___x_3476_);
                v___x_3478_ = lean_nat_dec_lt(v_numParams_3470_, v___x_3477_);
                if v___x_3478_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3476_);
                    crate::leanh::lean_dec(v_numParams_3470_);
                    crate::leanh::lean_del_object(v___x_3466_);
                    v___x_3479_ = crate::leanh::lean_box(0);
                    if v_isShared_3463_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3462_, 0, v___x_3479_);
                        v___x_3481_ = v___x_3462_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
                        v___x_3481_ = v_reuseFailAlloc_3482_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_3483_ = lean_array_fget(v___x_3476_, v_numParams_3470_);
                    crate::leanh::lean_dec(v_numParams_3470_);
                    crate::leanh::lean_dec_ref(v___x_3476_);
                    if v_isShared_3467_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3466_, 0, v___x_3483_);
                        v___x_3485_ = v___x_3466_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3483_);
                        v___x_3485_ = v_reuseFailAlloc_3489_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3481_;
            }
            6 => {
                if v_isShared_3463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3462_, 0, v___x_3485_);
                    v___x_3487_ = v___x_3462_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3487_;
            }
            8 => {
                return v___x_3493_;
            }
            9 => {
                if v_isShared_3499_ == 0 {
                    v___x_3501_ = v___x_3498_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3502_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
                    v___x_3501_ = v_reuseFailAlloc_3502_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_getInstanceProjectionArg_x3f___boxed(
    mut v_e_3506_: *mut crate::leanh::LeanObject,
    mut v_a_3507_: *mut crate::leanh::LeanObject,
    mut v_a_3508_: *mut crate::leanh::LeanObject,
    mut v_a_3509_: *mut crate::leanh::LeanObject,
    mut v_a_3510_: *mut crate::leanh::LeanObject,
    mut v_a_3511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Lean_Server_getInstanceProjectionArg_x3f(
        v_e_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_,
    );
    crate::leanh::lean_dec(v_a_3510_);
    crate::leanh::lean_dec_ref(v_a_3509_);
    crate::leanh::lean_dec(v_a_3508_);
    crate::leanh::lean_dec_ref(v_a_3507_);
    return v_res_3512_;
}
pub unsafe fn l_Lean_Server_isInstanceProjection(
    mut v_e_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
    mut v_a_3517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3524_: u8 = 0;
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut v_a_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3519_ = l_Lean_Server_getInstanceProjectionArg_x3f(
                    v_e_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_,
                );
                if crate::leanh::lean_obj_tag(v___x_3519_) == 0 {
                    v_a_3520_ = crate::leanh::lean_ctor_get(v___x_3519_, 0);
                    v_isSharedCheck_3534_ = (!crate::leanh::lean_is_exclusive(v___x_3519_)) as u8;
                    if v_isSharedCheck_3534_ == 0 {
                        v___x_3522_ = v___x_3519_;
                        v_isShared_3523_ = v_isSharedCheck_3534_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3520_);
                        crate::leanh::lean_dec(v___x_3519_);
                        v___x_3522_ = crate::leanh::lean_box(0);
                        v_isShared_3523_ = v_isSharedCheck_3534_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3535_ = crate::leanh::lean_ctor_get(v___x_3519_, 0);
                    v_isSharedCheck_3542_ = (!crate::leanh::lean_is_exclusive(v___x_3519_)) as u8;
                    if v_isSharedCheck_3542_ == 0 {
                        v___x_3537_ = v___x_3519_;
                        v_isShared_3538_ = v_isSharedCheck_3542_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3535_);
                        crate::leanh::lean_dec(v___x_3519_);
                        v___x_3537_ = crate::leanh::lean_box(0);
                        v_isShared_3538_ = v_isSharedCheck_3542_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3520_) == 0 {
                    v___x_3524_ = 0;
                    v___x_3525_ = crate::leanh::lean_box((v___x_3524_) as usize);
                    if v_isShared_3523_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3522_, 0, v___x_3525_);
                        v___x_3527_ = v___x_3522_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
                        v___x_3527_ = v_reuseFailAlloc_3528_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3520_, 1);
                    v___x_3529_ = 1;
                    v___x_3530_ = crate::leanh::lean_box((v___x_3529_) as usize);
                    if v_isShared_3523_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3522_, 0, v___x_3530_);
                        v___x_3532_ = v___x_3522_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
                        v___x_3532_ = v_reuseFailAlloc_3533_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3527_;
            }
            3 => {
                return v___x_3532_;
            }
            4 => {
                if v_isShared_3538_ == 0 {
                    v___x_3540_ = v___x_3537_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
                    v___x_3540_ = v_reuseFailAlloc_3541_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_isInstanceProjection___boxed(
    mut v_e_3543_: *mut crate::leanh::LeanObject,
    mut v_a_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3549_ =
        l_Lean_Server_isInstanceProjection(v_e_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_);
    crate::leanh::lean_dec(v_a_3547_);
    crate::leanh::lean_dec_ref(v_a_3546_);
    crate::leanh::lean_dec(v_a_3545_);
    crate::leanh::lean_dec_ref(v_a_3544_);
    return v_res_3549_;
}
pub unsafe fn l_Lean_Server_isInstanceProjectionInfoFor(
    mut v_kind_3550_: u8,
    mut v_ti1_3551_: *mut crate::leanh::LeanObject,
    mut v_ti2_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: u8 = 0;
    let mut v_toElabInfo_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: u8 = 0;
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v_expr_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___y_3594_: u8 = 0;
    let mut v___x_3595_: u8 = 0;
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v_isSharedCheck_3612_: u8 = 0;
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3617_: u8 = 0;
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3558_ = 2;
                v___x_3559_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_3550_, v___x_3558_);
                if v___x_3559_ == 0 {
                    v_toElabInfo_3560_ = crate::leanh::lean_ctor_get(v_ti1_3551_, 0);
                    crate::leanh::lean_inc_ref(v_toElabInfo_3560_);
                    v_expr_3561_ = crate::leanh::lean_ctor_get(v_ti1_3551_, 3);
                    crate::leanh::lean_inc_ref(v_expr_3561_);
                    crate::leanh::lean_dec_ref(v_ti1_3551_);
                    v_stx_3562_ = crate::leanh::lean_ctor_get(v_toElabInfo_3560_, 1);
                    crate::leanh::lean_inc(v_stx_3562_);
                    crate::leanh::lean_dec_ref(v_toElabInfo_3560_);
                    v___x_3563_ = 1;
                    v___x_3564_ = l_Lean_Syntax_getPos_x3f(v_stx_3562_, v___x_3563_);
                    crate::leanh::lean_dec(v_stx_3562_);
                    if crate::leanh::lean_obj_tag(v___x_3564_) == 1 {
                        v_toElabInfo_3565_ = crate::leanh::lean_ctor_get(v_ti2_3552_, 0);
                        crate::leanh::lean_inc_ref(v_toElabInfo_3565_);
                        v_val_3566_ = crate::leanh::lean_ctor_get(v___x_3564_, 0);
                        v_isSharedCheck_3622_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3564_)) as u8;
                        if v_isSharedCheck_3622_ == 0 {
                            v___x_3568_ = v___x_3564_;
                            v_isShared_3569_ = v_isSharedCheck_3622_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3566_);
                            crate::leanh::lean_dec(v___x_3564_);
                            v___x_3568_ = crate::leanh::lean_box(0);
                            v_isShared_3569_ = v_isSharedCheck_3622_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3564_);
                        crate::leanh::lean_dec_ref(v_expr_3561_);
                        crate::leanh::lean_dec_ref(v_ti2_3552_);
                        v___x_3623_ = crate::leanh::lean_box((v___x_3559_) as usize);
                        v___x_3624_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3624_, 0, v___x_3623_);
                        return v___x_3624_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ti2_3552_);
                    crate::leanh::lean_dec_ref(v_ti1_3551_);
                    v___x_3625_ = 0;
                    v___x_3626_ = crate::leanh::lean_box((v___x_3625_) as usize);
                    v___x_3627_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3627_, 0, v___x_3626_);
                    return v___x_3627_;
                }
            }
            1 => {
                v_expr_3570_ = crate::leanh::lean_ctor_get(v_ti2_3552_, 3);
                crate::leanh::lean_inc_ref(v_expr_3570_);
                crate::leanh::lean_dec_ref(v_ti2_3552_);
                v_stx_3571_ = crate::leanh::lean_ctor_get(v_toElabInfo_3565_, 1);
                crate::leanh::lean_inc(v_stx_3571_);
                crate::leanh::lean_dec_ref(v_toElabInfo_3565_);
                v___x_3572_ = l_Lean_Syntax_getPos_x3f(v_stx_3571_, v___x_3563_);
                crate::leanh::lean_dec(v_stx_3571_);
                if crate::leanh::lean_obj_tag(v___x_3572_) == 1 {
                    crate::leanh::lean_del_object(v___x_3568_);
                    v_val_3573_ = crate::leanh::lean_ctor_get(v___x_3572_, 0);
                    v_isSharedCheck_3617_ = (!crate::leanh::lean_is_exclusive(v___x_3572_)) as u8;
                    if v_isSharedCheck_3617_ == 0 {
                        v___x_3575_ = v___x_3572_;
                        v_isShared_3576_ = v_isSharedCheck_3617_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3573_);
                        crate::leanh::lean_dec(v___x_3572_);
                        v___x_3575_ = crate::leanh::lean_box(0);
                        v_isShared_3576_ = v_isSharedCheck_3617_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3572_);
                    crate::leanh::lean_dec_ref(v_expr_3570_);
                    crate::leanh::lean_dec(v_val_3566_);
                    crate::leanh::lean_dec_ref(v_expr_3561_);
                    v___x_3618_ = crate::leanh::lean_box((v___x_3559_) as usize);
                    if v_isShared_3569_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3568_, 0);
                        crate::leanh::lean_ctor_set(v___x_3568_, 0, v___x_3618_);
                        v___x_3620_ = v___x_3568_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3621_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
                        v___x_3620_ = v_reuseFailAlloc_3621_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3577_ = lean_nat_dec_eq(v_val_3566_, v_val_3573_);
                crate::leanh::lean_dec(v_val_3573_);
                crate::leanh::lean_dec(v_val_3566_);
                if v___x_3577_ == 0 {
                    crate::leanh::lean_dec_ref(v_expr_3570_);
                    crate::leanh::lean_dec_ref(v_expr_3561_);
                    v___x_3578_ = crate::leanh::lean_box((v___x_3559_) as usize);
                    if v_isShared_3576_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3575_, 0);
                        crate::leanh::lean_ctor_set(v___x_3575_, 0, v___x_3578_);
                        v___x_3580_ = v___x_3575_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
                        v___x_3580_ = v_reuseFailAlloc_3581_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v___x_3559_ == 0 {
                        crate::leanh::lean_del_object(v___x_3575_);
                        v___x_3582_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_3561_, v_a_3554_);
                        v_a_3583_ = crate::leanh::lean_ctor_get(v___x_3582_, 0);
                        crate::leanh::lean_inc_n(v_a_3583_, 2);
                        crate::leanh::lean_dec_ref(v___x_3582_);
                        v___x_3584_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_3570_, v_a_3554_);
                        v_a_3585_ = crate::leanh::lean_ctor_get(v___x_3584_, 0);
                        crate::leanh::lean_inc(v_a_3585_);
                        crate::leanh::lean_dec_ref(v___x_3584_);
                        v___x_3586_ = l_Lean_Server_isInstanceProjection(
                            v_a_3583_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3586_) == 0 {
                            v_a_3587_ = crate::leanh::lean_ctor_get(v___x_3586_, 0);
                            crate::leanh::lean_inc(v_a_3587_);
                            crate::leanh::lean_dec_ref_known(v___x_3586_, 1);
                            crate::leanh::lean_inc(v_a_3585_);
                            v___x_3588_ = l_Lean_Server_isInstanceProjection(
                                v_a_3585_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3588_) == 0 {
                                v_a_3589_ = crate::leanh::lean_ctor_get(v___x_3588_, 0);
                                v_isSharedCheck_3612_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3588_)) as u8;
                                if v_isSharedCheck_3612_ == 0 {
                                    v___x_3591_ = v___x_3588_;
                                    v_isShared_3592_ = v_isSharedCheck_3612_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3589_);
                                    crate::leanh::lean_dec(v___x_3588_);
                                    v___x_3591_ = crate::leanh::lean_box(0);
                                    v_isShared_3592_ = v_isSharedCheck_3612_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3587_);
                                crate::leanh::lean_dec(v_a_3585_);
                                crate::leanh::lean_dec(v_a_3583_);
                                return v___x_3588_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3585_);
                            crate::leanh::lean_dec(v_a_3583_);
                            return v___x_3586_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_expr_3570_);
                        crate::leanh::lean_dec_ref(v_expr_3561_);
                        v___x_3613_ = crate::leanh::lean_box((v___x_3559_) as usize);
                        if v_isShared_3576_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_3575_, 0);
                            crate::leanh::lean_ctor_set(v___x_3575_, 0, v___x_3613_);
                            v___x_3615_ = v___x_3575_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3616_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
                            v___x_3615_ = v_reuseFailAlloc_3616_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3580_;
            }
            4 => {
                v___x_3611_ = (crate::leanh::lean_unbox(v_a_3587_) as u8);
                crate::leanh::lean_dec(v_a_3587_);
                if v___x_3611_ == 0 {
                    v___y_3594_ = v___x_3577_;
                    state = 5;
                    continue;
                } else {
                    v___y_3594_ = v___x_3559_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_3594_ == 0 {
                    v___x_3595_ = (crate::leanh::lean_unbox(v_a_3589_) as u8);
                    crate::leanh::lean_dec(v_a_3589_);
                    if v___x_3595_ == 0 {
                        v___x_3596_ = l_Lean_Expr_getAppFn_x27(v_a_3583_);
                        crate::leanh::lean_dec(v_a_3583_);
                        v___x_3597_ = l_Lean_Expr_getAppFn_x27(v_a_3585_);
                        crate::leanh::lean_dec(v_a_3585_);
                        v___x_3598_ = lean_expr_eqv(v___x_3596_, v___x_3597_);
                        crate::leanh::lean_dec_ref(v___x_3597_);
                        crate::leanh::lean_dec_ref(v___x_3596_);
                        v___x_3599_ = crate::leanh::lean_box((v___x_3598_) as usize);
                        if v_isShared_3592_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3591_, 0, v___x_3599_);
                            v___x_3601_ = v___x_3591_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3602_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3599_);
                            v___x_3601_ = v_reuseFailAlloc_3602_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3585_);
                        crate::leanh::lean_dec(v_a_3583_);
                        v___x_3603_ = crate::leanh::lean_box((v___x_3559_) as usize);
                        if v_isShared_3592_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3591_, 0, v___x_3603_);
                            v___x_3605_ = v___x_3591_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3606_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
                            v___x_3605_ = v_reuseFailAlloc_3606_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3589_);
                    crate::leanh::lean_dec(v_a_3585_);
                    crate::leanh::lean_dec(v_a_3583_);
                    v___x_3607_ = crate::leanh::lean_box((v___x_3559_) as usize);
                    if v_isShared_3592_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3591_, 0, v___x_3607_);
                        v___x_3609_ = v___x_3591_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3610_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
                        v___x_3609_ = v_reuseFailAlloc_3610_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3601_;
            }
            7 => {
                return v___x_3605_;
            }
            8 => {
                return v___x_3609_;
            }
            9 => {
                return v___x_3615_;
            }
            10 => {
                return v___x_3620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_isInstanceProjectionInfoFor___boxed(
    mut v_kind_3628_: *mut crate::leanh::LeanObject,
    mut v_ti1_3629_: *mut crate::leanh::LeanObject,
    mut v_ti2_3630_: *mut crate::leanh::LeanObject,
    mut v_a_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
    mut v_a_3633_: *mut crate::leanh::LeanObject,
    mut v_a_3634_: *mut crate::leanh::LeanObject,
    mut v_a_3635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_3636_: u8 = 0;
    let mut v_res_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3636_ = (crate::leanh::lean_unbox(v_kind_3628_) as u8);
    v_res_3637_ = l_Lean_Server_isInstanceProjectionInfoFor(
        v_kind_boxed_3636_,
        v_ti1_3629_,
        v_ti2_3630_,
        v_a_3631_,
        v_a_3632_,
        v_a_3633_,
        v_a_3634_,
    );
    crate::leanh::lean_dec(v_a_3634_);
    crate::leanh::lean_dec_ref(v_a_3633_);
    crate::leanh::lean_dec(v_a_3632_);
    crate::leanh::lean_dec_ref(v_a_3631_);
    return v_res_3637_;
}
pub unsafe fn l_Lean_Server_GoToM_run___redArg(
    mut v_ctx_3638_: *mut crate::leanh::LeanObject,
    mut v_ci_3639_: *mut crate::leanh::LeanObject,
    mut v_lctx_3640_: *mut crate::leanh::LeanObject,
    mut v_act_3641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3643_ = crate::leanh::lean_apply_1(v_act_3641_, v_ctx_3638_);
    v___x_3644_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_3639_, v_lctx_3640_, v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_Lean_Server_GoToM_run___redArg___boxed(
    mut v_ctx_3645_: *mut crate::leanh::LeanObject,
    mut v_ci_3646_: *mut crate::leanh::LeanObject,
    mut v_lctx_3647_: *mut crate::leanh::LeanObject,
    mut v_act_3648_: *mut crate::leanh::LeanObject,
    mut v_a_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ =
        l_Lean_Server_GoToM_run___redArg(v_ctx_3645_, v_ci_3646_, v_lctx_3647_, v_act_3648_);
    return v_res_3650_;
}
pub unsafe fn l_Lean_Server_GoToM_run(
    mut v_00_u03b1_3651_: *mut crate::leanh::LeanObject,
    mut v_ctx_3652_: *mut crate::leanh::LeanObject,
    mut v_ci_3653_: *mut crate::leanh::LeanObject,
    mut v_lctx_3654_: *mut crate::leanh::LeanObject,
    mut v_act_3655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3657_ =
        l_Lean_Server_GoToM_run___redArg(v_ctx_3652_, v_ci_3653_, v_lctx_3654_, v_act_3655_);
    return v___x_3657_;
}
pub unsafe fn l_Lean_Server_GoToM_run___boxed(
    mut v_00_u03b1_3658_: *mut crate::leanh::LeanObject,
    mut v_ctx_3659_: *mut crate::leanh::LeanObject,
    mut v_ci_3660_: *mut crate::leanh::LeanObject,
    mut v_lctx_3661_: *mut crate::leanh::LeanObject,
    mut v_act_3662_: *mut crate::leanh::LeanObject,
    mut v_a_3663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3664_ = l_Lean_Server_GoToM_run(
        v_00_u03b1_3658_,
        v_ctx_3659_,
        v_ci_3660_,
        v_lctx_3661_,
        v_act_3662_,
    );
    return v_res_3664_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(
    mut v_msgData_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3671_ = lean_st_ref_get(v___y_3669_);
    v_env_3672_ = crate::leanh::lean_ctor_get(v___x_3671_, 0);
    crate::leanh::lean_inc_ref(v_env_3672_);
    crate::leanh::lean_dec(v___x_3671_);
    v___x_3673_ = lean_st_ref_get(v___y_3667_);
    v_mctx_3674_ = crate::leanh::lean_ctor_get(v___x_3673_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3674_);
    crate::leanh::lean_dec(v___x_3673_);
    v_lctx_3675_ = crate::leanh::lean_ctor_get(v___y_3666_, 2);
    v_options_3676_ = crate::leanh::lean_ctor_get(v___y_3668_, 2);
    crate::leanh::lean_inc_ref(v_options_3676_);
    crate::leanh::lean_inc_ref(v_lctx_3675_);
    v___x_3677_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3677_, 0, v_env_3672_);
    crate::leanh::lean_ctor_set(v___x_3677_, 1, v_mctx_3674_);
    crate::leanh::lean_ctor_set(v___x_3677_, 2, v_lctx_3675_);
    crate::leanh::lean_ctor_set(v___x_3677_, 3, v_options_3676_);
    v___x_3678_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3678_, 0, v___x_3677_);
    crate::leanh::lean_ctor_set(v___x_3678_, 1, v_msgData_3665_);
    v___x_3679_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3679_, 0, v___x_3678_);
    return v___x_3679_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(
    mut v_msgData_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
    crate::leanh::lean_dec(v___y_3684_);
    crate::leanh::lean_dec_ref(v___y_3683_);
    crate::leanh::lean_dec(v___y_3682_);
    crate::leanh::lean_dec_ref(v___y_3681_);
    return v_res_3686_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(
    mut v_msg_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
    mut v___y_3689_: *mut crate::leanh::LeanObject,
    mut v___y_3690_: *mut crate::leanh::LeanObject,
    mut v___y_3691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3693_ = crate::leanh::lean_ctor_get(v___y_3690_, 5);
                v___x_3694_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
                v_a_3695_ = crate::leanh::lean_ctor_get(v___x_3694_, 0);
                v_isSharedCheck_3703_ = (!crate::leanh::lean_is_exclusive(v___x_3694_)) as u8;
                if v_isSharedCheck_3703_ == 0 {
                    v___x_3697_ = v___x_3694_;
                    v_isShared_3698_ = v_isSharedCheck_3703_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3695_);
                    crate::leanh::lean_dec(v___x_3694_);
                    v___x_3697_ = crate::leanh::lean_box(0);
                    v_isShared_3698_ = v_isSharedCheck_3703_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3693_);
                v___x_3699_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3699_, 0, v_ref_3693_);
                crate::leanh::lean_ctor_set(v___x_3699_, 1, v_a_3695_);
                if v_isShared_3698_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3697_, 1);
                    crate::leanh::lean_ctor_set(v___x_3697_, 0, v___x_3699_);
                    v___x_3701_ = v___x_3697_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
                    v___x_3701_ = v_reuseFailAlloc_3702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_msg_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
    mut v___y_3709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3710_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
    crate::leanh::lean_dec(v___y_3708_);
    crate::leanh::lean_dec_ref(v___y_3707_);
    crate::leanh::lean_dec(v___y_3706_);
    crate::leanh::lean_dec_ref(v___y_3705_);
    return v_res_3710_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_ref_3711_: *mut crate::leanh::LeanObject,
    mut v_msg_3712_: *mut crate::leanh::LeanObject,
    mut v___y_3713_: *mut crate::leanh::LeanObject,
    mut v___y_3714_: *mut crate::leanh::LeanObject,
    mut v___y_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3731_: u8 = 0;
    let mut v_cancelTk_x3f_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3733_: u8 = 0;
    let mut v_inheritedTraceOptions_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3719_ = crate::leanh::lean_ctor_get(v___y_3716_, 0);
    v_fileMap_3720_ = crate::leanh::lean_ctor_get(v___y_3716_, 1);
    v_options_3721_ = crate::leanh::lean_ctor_get(v___y_3716_, 2);
    v_currRecDepth_3722_ = crate::leanh::lean_ctor_get(v___y_3716_, 3);
    v_maxRecDepth_3723_ = crate::leanh::lean_ctor_get(v___y_3716_, 4);
    v_ref_3724_ = crate::leanh::lean_ctor_get(v___y_3716_, 5);
    v_currNamespace_3725_ = crate::leanh::lean_ctor_get(v___y_3716_, 6);
    v_openDecls_3726_ = crate::leanh::lean_ctor_get(v___y_3716_, 7);
    v_initHeartbeats_3727_ = crate::leanh::lean_ctor_get(v___y_3716_, 8);
    v_maxHeartbeats_3728_ = crate::leanh::lean_ctor_get(v___y_3716_, 9);
    v_quotContext_3729_ = crate::leanh::lean_ctor_get(v___y_3716_, 10);
    v_currMacroScope_3730_ = crate::leanh::lean_ctor_get(v___y_3716_, 11);
    v_diag_3731_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3716_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3732_ = crate::leanh::lean_ctor_get(v___y_3716_, 12);
    v_suppressElabErrors_3733_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3716_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3734_ = crate::leanh::lean_ctor_get(v___y_3716_, 13);
    v_ref_3735_ = l_Lean_replaceRef(v_ref_3711_, v_ref_3724_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3734_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3732_);
    crate::leanh::lean_inc(v_currMacroScope_3730_);
    crate::leanh::lean_inc(v_quotContext_3729_);
    crate::leanh::lean_inc(v_maxHeartbeats_3728_);
    crate::leanh::lean_inc(v_initHeartbeats_3727_);
    crate::leanh::lean_inc(v_openDecls_3726_);
    crate::leanh::lean_inc(v_currNamespace_3725_);
    crate::leanh::lean_inc(v_maxRecDepth_3723_);
    crate::leanh::lean_inc(v_currRecDepth_3722_);
    crate::leanh::lean_inc_ref(v_options_3721_);
    crate::leanh::lean_inc_ref(v_fileMap_3720_);
    crate::leanh::lean_inc_ref(v_fileName_3719_);
    v___x_3736_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3736_, 0, v_fileName_3719_);
    crate::leanh::lean_ctor_set(v___x_3736_, 1, v_fileMap_3720_);
    crate::leanh::lean_ctor_set(v___x_3736_, 2, v_options_3721_);
    crate::leanh::lean_ctor_set(v___x_3736_, 3, v_currRecDepth_3722_);
    crate::leanh::lean_ctor_set(v___x_3736_, 4, v_maxRecDepth_3723_);
    crate::leanh::lean_ctor_set(v___x_3736_, 5, v_ref_3735_);
    crate::leanh::lean_ctor_set(v___x_3736_, 6, v_currNamespace_3725_);
    crate::leanh::lean_ctor_set(v___x_3736_, 7, v_openDecls_3726_);
    crate::leanh::lean_ctor_set(v___x_3736_, 8, v_initHeartbeats_3727_);
    crate::leanh::lean_ctor_set(v___x_3736_, 9, v_maxHeartbeats_3728_);
    crate::leanh::lean_ctor_set(v___x_3736_, 10, v_quotContext_3729_);
    crate::leanh::lean_ctor_set(v___x_3736_, 11, v_currMacroScope_3730_);
    crate::leanh::lean_ctor_set(v___x_3736_, 12, v_cancelTk_x3f_3732_);
    crate::leanh::lean_ctor_set(v___x_3736_, 13, v_inheritedTraceOptions_3734_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3736_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3731_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3736_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3733_,
    );
    v___x_3737_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_3712_, v___y_3714_, v___y_3715_, v___x_3736_, v___y_3717_);
    crate::leanh::lean_dec_ref_known(v___x_3736_, 14);
    return v___x_3737_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_ref_3738_: *mut crate::leanh::LeanObject,
    mut v_msg_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
    mut v___y_3741_: *mut crate::leanh::LeanObject,
    mut v___y_3742_: *mut crate::leanh::LeanObject,
    mut v___y_3743_: *mut crate::leanh::LeanObject,
    mut v___y_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3746_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3738_, v_msg_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
    crate::leanh::lean_dec(v___y_3744_);
    crate::leanh::lean_dec_ref(v___y_3743_);
    crate::leanh::lean_dec(v___y_3742_);
    crate::leanh::lean_dec_ref(v___y_3741_);
    crate::leanh::lean_dec_ref(v___y_3740_);
    crate::leanh::lean_dec(v_ref_3738_);
    return v_res_3746_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3747_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3747_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3748_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
    v___x_3749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3749_, 0, v___x_3748_);
    return v___x_3749_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3750_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_3751_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3752_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3752_, 0, v___x_3751_);
    crate::leanh::lean_ctor_set(v___x_3752_, 1, v___x_3751_);
    crate::leanh::lean_ctor_set(v___x_3752_, 2, v___x_3751_);
    crate::leanh::lean_ctor_set(v___x_3752_, 3, v___x_3751_);
    crate::leanh::lean_ctor_set(v___x_3752_, 4, v___x_3750_);
    crate::leanh::lean_ctor_set(v___x_3752_, 5, v___x_3750_);
    crate::leanh::lean_ctor_set(v___x_3752_, 6, v___x_3750_);
    crate::leanh::lean_ctor_set(v___x_3752_, 7, v___x_3750_);
    crate::leanh::lean_ctor_set(v___x_3752_, 8, v___x_3750_);
    crate::leanh::lean_ctor_set(v___x_3752_, 9, v___x_3750_);
    return v___x_3752_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3753_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3754_ = lean_mk_empty_array_with_capacity(v___x_3753_);
    v___x_3755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3755_, 0, v___x_3754_);
    return v___x_3755_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3756_: usize = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3756_ = 5usize;
    v___x_3757_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3758_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3759_ = lean_mk_empty_array_with_capacity(v___x_3758_);
    v___x_3760_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
    v___x_3761_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3761_, 0, v___x_3760_);
    crate::leanh::lean_ctor_set(v___x_3761_, 1, v___x_3759_);
    crate::leanh::lean_ctor_set(v___x_3761_, 2, v___x_3757_);
    crate::leanh::lean_ctor_set(v___x_3761_, 3, v___x_3757_);
    crate::leanh::lean_ctor_set_usize(v___x_3761_, 4, v___x_3756_);
    return v___x_3761_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3762_ = crate::leanh::lean_box(1);
    v___x_3763_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_3764_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_3765_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3765_, 0, v___x_3764_);
    crate::leanh::lean_ctor_set(v___x_3765_, 1, v___x_3763_);
    crate::leanh::lean_ctor_set(v___x_3765_, 2, v___x_3762_);
    return v___x_3765_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3767_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6;
    v___x_3768_ = l_Lean_stringToMessageData(v___x_3767_);
    return v___x_3768_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3770_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8;
    v___x_3771_ = l_Lean_stringToMessageData(v___x_3770_);
    return v___x_3771_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3773_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10;
    v___x_3774_ = l_Lean_stringToMessageData(v___x_3773_);
    return v___x_3774_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12;
    v___x_3777_ = l_Lean_stringToMessageData(v___x_3776_);
    return v___x_3777_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14;
    v___x_3780_ = l_Lean_stringToMessageData(v___x_3779_);
    return v___x_3780_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3782_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16;
    v___x_3783_ = l_Lean_stringToMessageData(v___x_3782_);
    return v___x_3783_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18;
    v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_msg_3787_: *mut crate::leanh::LeanObject,
    mut v_declHint_3788_: *mut crate::leanh::LeanObject,
    mut v___y_3789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: u8 = 0;
    let mut v_isExporting_3794_: u8 = 0;
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3816_: u8 = 0;
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3791_ = lean_st_ref_get(v___y_3789_);
                v_env_3792_ = crate::leanh::lean_ctor_get(v___x_3791_, 0);
                crate::leanh::lean_inc_ref(v_env_3792_);
                crate::leanh::lean_dec(v___x_3791_);
                v___x_3793_ = l_Lean_Name_isAnonymous(v_declHint_3788_);
                if v___x_3793_ == 0 {
                    v_isExporting_3794_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_3792_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3794_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_3792_);
                        crate::leanh::lean_dec(v_declHint_3788_);
                        v___x_3795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3795_, 0, v_msg_3787_);
                        return v___x_3795_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_3792_);
                        v___x_3796_ = l_Lean_Environment_setExporting(v_env_3792_, v___x_3793_);
                        crate::leanh::lean_inc(v_declHint_3788_);
                        crate::leanh::lean_inc_ref(v___x_3796_);
                        v___x_3797_ = l_Lean_Environment_contains(
                            v___x_3796_,
                            v_declHint_3788_,
                            v_isExporting_3794_,
                        );
                        if v___x_3797_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3796_);
                            crate::leanh::lean_dec_ref(v_env_3792_);
                            crate::leanh::lean_dec(v_declHint_3788_);
                            v___x_3798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3798_, 0, v_msg_3787_);
                            return v___x_3798_;
                        } else {
                            v___x_3799_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
                            v___x_3800_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
                            v___x_3801_ = l_Lean_Options_empty;
                            v___x_3802_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3802_, 0, v___x_3796_);
                            crate::leanh::lean_ctor_set(v___x_3802_, 1, v___x_3799_);
                            crate::leanh::lean_ctor_set(v___x_3802_, 2, v___x_3800_);
                            crate::leanh::lean_ctor_set(v___x_3802_, 3, v___x_3801_);
                            crate::leanh::lean_inc(v_declHint_3788_);
                            v___x_3803_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3788_, v___x_3793_);
                            v_c_3804_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_3804_, 0, v___x_3802_);
                            crate::leanh::lean_ctor_set(v_c_3804_, 1, v___x_3803_);
                            v___x_3805_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3792_,
                                v_declHint_3788_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3805_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_3792_);
                                crate::leanh::lean_dec(v_declHint_3788_);
                                v___x_3806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                                v___x_3807_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3807_, 0, v___x_3806_);
                                crate::leanh::lean_ctor_set(v___x_3807_, 1, v_c_3804_);
                                v___x_3808_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
                                v___x_3809_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3809_, 0, v___x_3807_);
                                crate::leanh::lean_ctor_set(v___x_3809_, 1, v___x_3808_);
                                v___x_3810_ = l_Lean_MessageData_note(v___x_3809_);
                                v___x_3811_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3811_, 0, v_msg_3787_);
                                crate::leanh::lean_ctor_set(v___x_3811_, 1, v___x_3810_);
                                v___x_3812_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3812_, 0, v___x_3811_);
                                return v___x_3812_;
                            } else {
                                v_val_3813_ = crate::leanh::lean_ctor_get(v___x_3805_, 0);
                                v_isSharedCheck_3848_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3805_)) as u8;
                                if v_isSharedCheck_3848_ == 0 {
                                    v___x_3815_ = v___x_3805_;
                                    v_isShared_3816_ = v_isSharedCheck_3848_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3813_);
                                    crate::leanh::lean_dec(v___x_3805_);
                                    v___x_3815_ = crate::leanh::lean_box(0);
                                    v_isShared_3816_ = v_isSharedCheck_3848_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3792_);
                    crate::leanh::lean_dec(v_declHint_3788_);
                    v___x_3849_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3849_, 0, v_msg_3787_);
                    return v___x_3849_;
                }
            }
            1 => {
                v___x_3817_ = crate::leanh::lean_box(0);
                v___x_3818_ = l_Lean_Environment_header(v_env_3792_);
                crate::leanh::lean_dec_ref(v_env_3792_);
                v___x_3819_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3818_);
                v_mod_3820_ = lean_array_get(v___x_3817_, v___x_3819_, v_val_3813_);
                crate::leanh::lean_dec(v_val_3813_);
                crate::leanh::lean_dec_ref(v___x_3819_);
                v___x_3821_ = l_Lean_isPrivateName(v_declHint_3788_);
                crate::leanh::lean_dec(v_declHint_3788_);
                if v___x_3821_ == 0 {
                    v___x_3822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
                    v___x_3823_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3823_, 0, v___x_3822_);
                    crate::leanh::lean_ctor_set(v___x_3823_, 1, v_c_3804_);
                    v___x_3824_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
                    v___x_3825_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3825_, 0, v___x_3823_);
                    crate::leanh::lean_ctor_set(v___x_3825_, 1, v___x_3824_);
                    v___x_3826_ = l_Lean_MessageData_ofName(v_mod_3820_);
                    v___x_3827_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3827_, 0, v___x_3825_);
                    crate::leanh::lean_ctor_set(v___x_3827_, 1, v___x_3826_);
                    v___x_3828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
                    v___x_3829_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3829_, 0, v___x_3827_);
                    crate::leanh::lean_ctor_set(v___x_3829_, 1, v___x_3828_);
                    v___x_3830_ = l_Lean_MessageData_note(v___x_3829_);
                    v___x_3831_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3831_, 0, v_msg_3787_);
                    crate::leanh::lean_ctor_set(v___x_3831_, 1, v___x_3830_);
                    if v_isShared_3816_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3815_, 0);
                        crate::leanh::lean_ctor_set(v___x_3815_, 0, v___x_3831_);
                        v___x_3833_ = v___x_3815_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
                        v___x_3833_ = v_reuseFailAlloc_3834_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3835_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                    v___x_3836_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3836_, 0, v___x_3835_);
                    crate::leanh::lean_ctor_set(v___x_3836_, 1, v_c_3804_);
                    v___x_3837_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
                    v___x_3838_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3838_, 0, v___x_3836_);
                    crate::leanh::lean_ctor_set(v___x_3838_, 1, v___x_3837_);
                    v___x_3839_ = l_Lean_MessageData_ofName(v_mod_3820_);
                    v___x_3840_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3840_, 0, v___x_3838_);
                    crate::leanh::lean_ctor_set(v___x_3840_, 1, v___x_3839_);
                    v___x_3841_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
                    v___x_3842_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3842_, 0, v___x_3840_);
                    crate::leanh::lean_ctor_set(v___x_3842_, 1, v___x_3841_);
                    v___x_3843_ = l_Lean_MessageData_note(v___x_3842_);
                    v___x_3844_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3844_, 0, v_msg_3787_);
                    crate::leanh::lean_ctor_set(v___x_3844_, 1, v___x_3843_);
                    if v_isShared_3816_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3815_, 0);
                        crate::leanh::lean_ctor_set(v___x_3815_, 0, v___x_3844_);
                        v___x_3846_ = v___x_3815_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3847_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
                        v___x_3846_ = v_reuseFailAlloc_3847_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3833_;
            }
            3 => {
                return v___x_3846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_msg_3850_: *mut crate::leanh::LeanObject,
    mut v_declHint_3851_: *mut crate::leanh::LeanObject,
    mut v___y_3852_: *mut crate::leanh::LeanObject,
    mut v___y_3853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3854_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_3850_, v_declHint_3851_, v___y_3852_);
    crate::leanh::lean_dec(v___y_3852_);
    return v_res_3854_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_3855_: *mut crate::leanh::LeanObject,
    mut v_declHint_3856_: *mut crate::leanh::LeanObject,
    mut v___y_3857_: *mut crate::leanh::LeanObject,
    mut v___y_3858_: *mut crate::leanh::LeanObject,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3863_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_3855_, v_declHint_3856_, v___y_3861_);
                v_a_3864_ = crate::leanh::lean_ctor_get(v___x_3863_, 0);
                v_isSharedCheck_3873_ = (!crate::leanh::lean_is_exclusive(v___x_3863_)) as u8;
                if v_isSharedCheck_3873_ == 0 {
                    v___x_3866_ = v___x_3863_;
                    v_isShared_3867_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3864_);
                    crate::leanh::lean_dec(v___x_3863_);
                    v___x_3866_ = crate::leanh::lean_box(0);
                    v_isShared_3867_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3868_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3869_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3869_, 0, v___x_3868_);
                crate::leanh::lean_ctor_set(v___x_3869_, 1, v_a_3864_);
                if v_isShared_3867_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3866_, 0, v___x_3869_);
                    v___x_3871_ = v___x_3866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3869_);
                    v___x_3871_ = v_reuseFailAlloc_3872_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_3874_: *mut crate::leanh::LeanObject,
    mut v_declHint_3875_: *mut crate::leanh::LeanObject,
    mut v___y_3876_: *mut crate::leanh::LeanObject,
    mut v___y_3877_: *mut crate::leanh::LeanObject,
    mut v___y_3878_: *mut crate::leanh::LeanObject,
    mut v___y_3879_: *mut crate::leanh::LeanObject,
    mut v___y_3880_: *mut crate::leanh::LeanObject,
    mut v___y_3881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3882_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3874_, v_declHint_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
    crate::leanh::lean_dec(v___y_3880_);
    crate::leanh::lean_dec_ref(v___y_3879_);
    crate::leanh::lean_dec(v___y_3878_);
    crate::leanh::lean_dec_ref(v___y_3877_);
    crate::leanh::lean_dec_ref(v___y_3876_);
    return v_res_3882_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_ref_3883_: *mut crate::leanh::LeanObject,
    mut v_msg_3884_: *mut crate::leanh::LeanObject,
    mut v_declHint_3885_: *mut crate::leanh::LeanObject,
    mut v___y_3886_: *mut crate::leanh::LeanObject,
    mut v___y_3887_: *mut crate::leanh::LeanObject,
    mut v___y_3888_: *mut crate::leanh::LeanObject,
    mut v___y_3889_: *mut crate::leanh::LeanObject,
    mut v___y_3890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3892_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3884_, v_declHint_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
    v_a_3893_ = crate::leanh::lean_ctor_get(v___x_3892_, 0);
    crate::leanh::lean_inc(v_a_3893_);
    crate::leanh::lean_dec_ref(v___x_3892_);
    v___x_3894_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3883_, v_a_3893_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
    return v___x_3894_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_ref_3895_: *mut crate::leanh::LeanObject,
    mut v_msg_3896_: *mut crate::leanh::LeanObject,
    mut v_declHint_3897_: *mut crate::leanh::LeanObject,
    mut v___y_3898_: *mut crate::leanh::LeanObject,
    mut v___y_3899_: *mut crate::leanh::LeanObject,
    mut v___y_3900_: *mut crate::leanh::LeanObject,
    mut v___y_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
    mut v___y_3903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_3895_, v_msg_3896_, v_declHint_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
    crate::leanh::lean_dec(v___y_3902_);
    crate::leanh::lean_dec_ref(v___y_3901_);
    crate::leanh::lean_dec(v___y_3900_);
    crate::leanh::lean_dec_ref(v___y_3899_);
    crate::leanh::lean_dec_ref(v___y_3898_);
    crate::leanh::lean_dec(v_ref_3895_);
    return v_res_3904_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3906_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0;
    v___x_3907_ = l_Lean_stringToMessageData(v___x_3906_);
    return v___x_3907_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3909_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2;
    v___x_3910_ = l_Lean_stringToMessageData(v___x_3909_);
    return v___x_3910_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_3911_: *mut crate::leanh::LeanObject,
    mut v_constName_3912_: *mut crate::leanh::LeanObject,
    mut v___y_3913_: *mut crate::leanh::LeanObject,
    mut v___y_3914_: *mut crate::leanh::LeanObject,
    mut v___y_3915_: *mut crate::leanh::LeanObject,
    mut v___y_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: u8 = 0;
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3919_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
    v___x_3920_ = 0;
    crate::leanh::lean_inc(v_constName_3912_);
    v___x_3921_ = l_Lean_MessageData_ofConstName(v_constName_3912_, v___x_3920_);
    v___x_3922_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3922_, 0, v___x_3919_);
    crate::leanh::lean_ctor_set(v___x_3922_, 1, v___x_3921_);
    v___x_3923_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
    v___x_3924_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3924_, 0, v___x_3922_);
    crate::leanh::lean_ctor_set(v___x_3924_, 1, v___x_3923_);
    v___x_3925_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_3911_, v___x_3924_, v_constName_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
    return v___x_3925_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_3926_: *mut crate::leanh::LeanObject,
    mut v_constName_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
    mut v___y_3932_: *mut crate::leanh::LeanObject,
    mut v___y_3933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3934_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3926_, v_constName_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
    crate::leanh::lean_dec(v___y_3932_);
    crate::leanh::lean_dec_ref(v___y_3931_);
    crate::leanh::lean_dec(v___y_3930_);
    crate::leanh::lean_dec_ref(v___y_3929_);
    crate::leanh::lean_dec_ref(v___y_3928_);
    crate::leanh::lean_dec(v_ref_3926_);
    return v_res_3934_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_constName_3935_: *mut crate::leanh::LeanObject,
    mut v___y_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
    mut v___y_3938_: *mut crate::leanh::LeanObject,
    mut v___y_3939_: *mut crate::leanh::LeanObject,
    mut v___y_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3942_ = crate::leanh::lean_ctor_get(v___y_3939_, 5);
    v___x_3943_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3942_, v_constName_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
    return v___x_3943_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_constName_3944_: *mut crate::leanh::LeanObject,
    mut v___y_3945_: *mut crate::leanh::LeanObject,
    mut v___y_3946_: *mut crate::leanh::LeanObject,
    mut v___y_3947_: *mut crate::leanh::LeanObject,
    mut v___y_3948_: *mut crate::leanh::LeanObject,
    mut v___y_3949_: *mut crate::leanh::LeanObject,
    mut v___y_3950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3951_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
    crate::leanh::lean_dec(v___y_3949_);
    crate::leanh::lean_dec_ref(v___y_3948_);
    crate::leanh::lean_dec(v___y_3947_);
    crate::leanh::lean_dec_ref(v___y_3946_);
    crate::leanh::lean_dec_ref(v___y_3945_);
    return v_res_3951_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(
    mut v_constName_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
    mut v___y_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: u8 = 0;
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3967_: u8 = 0;
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3959_ = lean_st_ref_get(v___y_3957_);
                v_env_3960_ = crate::leanh::lean_ctor_get(v___x_3959_, 0);
                crate::leanh::lean_inc_ref(v_env_3960_);
                crate::leanh::lean_dec(v___x_3959_);
                v___x_3961_ = 0;
                crate::leanh::lean_inc(v_constName_3952_);
                v___x_3962_ =
                    l_Lean_Environment_find_x3f(v_env_3960_, v_constName_3952_, v___x_3961_);
                if crate::leanh::lean_obj_tag(v___x_3962_) == 0 {
                    v___x_3963_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
                    return v___x_3963_;
                } else {
                    crate::leanh::lean_dec(v_constName_3952_);
                    v_val_3964_ = crate::leanh::lean_ctor_get(v___x_3962_, 0);
                    v_isSharedCheck_3971_ = (!crate::leanh::lean_is_exclusive(v___x_3962_)) as u8;
                    if v_isSharedCheck_3971_ == 0 {
                        v___x_3966_ = v___x_3962_;
                        v_isShared_3967_ = v_isSharedCheck_3971_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3964_);
                        crate::leanh::lean_dec(v___x_3962_);
                        v___x_3966_ = crate::leanh::lean_box(0);
                        v_isShared_3967_ = v_isSharedCheck_3971_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3967_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3966_, 0);
                    v___x_3969_ = v___x_3966_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3970_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_val_3964_);
                    v___x_3969_ = v_reuseFailAlloc_3970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0___boxed(
    mut v_constName_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_constName_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
    crate::leanh::lean_dec(v___y_3977_);
    crate::leanh::lean_dec_ref(v___y_3976_);
    crate::leanh::lean_dec(v___y_3975_);
    crate::leanh::lean_dec_ref(v___y_3974_);
    crate::leanh::lean_dec_ref(v___y_3973_);
    return v_res_3979_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(
    mut v_declName_3980_: *mut crate::leanh::LeanObject,
    mut v___y_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4001_: u8 = 0;
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut v_isSharedCheck_4014_: u8 = 0;
    let mut v_unused_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4019_: u8 = 0;
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_3980_);
                v___x_3987_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_declName_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
                if crate::leanh::lean_obj_tag(v___x_3987_) == 0 {
                    v_isSharedCheck_4014_ = (!crate::leanh::lean_is_exclusive(v___x_3987_)) as u8;
                    if v_isSharedCheck_4014_ == 0 {
                        v_unused_4015_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                        crate::leanh::lean_dec(v_unused_4015_);
                        v___x_3989_ = v___x_3987_;
                        v_isShared_3990_ = v_isSharedCheck_4014_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3987_);
                        v___x_3989_ = crate::leanh::lean_box(0);
                        v_isShared_3990_ = v_isSharedCheck_4014_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_3980_);
                    v_a_4016_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                    v_isSharedCheck_4023_ = (!crate::leanh::lean_is_exclusive(v___x_3987_)) as u8;
                    if v_isSharedCheck_4023_ == 0 {
                        v___x_4018_ = v___x_3987_;
                        v_isShared_4019_ = v_isSharedCheck_4023_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4016_);
                        crate::leanh::lean_dec(v___x_3987_);
                        v___x_4018_ = crate::leanh::lean_box(0);
                        v_isShared_4019_ = v_isSharedCheck_4023_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3991_ = lean_st_ref_get(v___y_3985_);
                v_env_3992_ = crate::leanh::lean_ctor_get(v___x_3991_, 0);
                crate::leanh::lean_inc_ref(v_env_3992_);
                crate::leanh::lean_dec(v___x_3991_);
                v___x_3993_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3992_, v_declName_3980_);
                crate::leanh::lean_dec(v_declName_3980_);
                crate::leanh::lean_dec_ref(v_env_3992_);
                if crate::leanh::lean_obj_tag(v___x_3993_) == 0 {
                    v___x_3994_ = crate::leanh::lean_box(0);
                    if v_isShared_3990_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3989_, 0, v___x_3994_);
                        v___x_3996_ = v___x_3989_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3997_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3994_);
                        v___x_3996_ = v_reuseFailAlloc_3997_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3998_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                    v_isSharedCheck_4013_ = (!crate::leanh::lean_is_exclusive(v___x_3993_)) as u8;
                    if v_isSharedCheck_4013_ == 0 {
                        v___x_4000_ = v___x_3993_;
                        v_isShared_4001_ = v_isSharedCheck_4013_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3998_);
                        crate::leanh::lean_dec(v___x_3993_);
                        v___x_4000_ = crate::leanh::lean_box(0);
                        v_isShared_4001_ = v_isSharedCheck_4013_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3996_;
            }
            3 => {
                v___x_4002_ = lean_st_ref_get(v___y_3985_);
                v_env_4003_ = crate::leanh::lean_ctor_get(v___x_4002_, 0);
                crate::leanh::lean_inc_ref(v_env_4003_);
                crate::leanh::lean_dec(v___x_4002_);
                v___x_4004_ = crate::leanh::lean_box(0);
                v___x_4005_ = l_Lean_Environment_allImportedModuleNames(v_env_4003_);
                crate::leanh::lean_dec_ref(v_env_4003_);
                v___x_4006_ = lean_array_get(v___x_4004_, v___x_4005_, v_val_3998_);
                crate::leanh::lean_dec(v_val_3998_);
                crate::leanh::lean_dec_ref(v___x_4005_);
                if v_isShared_4001_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4000_, 0, v___x_4006_);
                    v___x_4008_ = v___x_4000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4012_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4006_);
                    v___x_4008_ = v_reuseFailAlloc_4012_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3989_, 0, v___x_4008_);
                    v___x_4010_ = v___x_3989_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4008_);
                    v___x_4010_ = v_reuseFailAlloc_4011_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4010_;
            }
            6 => {
                if v_isShared_4019_ == 0 {
                    v___x_4021_ = v___x_4018_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
                    v___x_4021_ = v_reuseFailAlloc_4022_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0___boxed(
    mut v_declName_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
    mut v___y_4027_: *mut crate::leanh::LeanObject,
    mut v___y_4028_: *mut crate::leanh::LeanObject,
    mut v___y_4029_: *mut crate::leanh::LeanObject,
    mut v___y_4030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4031_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
    crate::leanh::lean_dec(v___y_4029_);
    crate::leanh::lean_dec_ref(v___y_4028_);
    crate::leanh::lean_dec(v___y_4027_);
    crate::leanh::lean_dec_ref(v___y_4026_);
    crate::leanh::lean_dec_ref(v___y_4025_);
    return v_res_4031_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(
    mut v_declName_4032_: *mut crate::leanh::LeanObject,
    mut v_a_4033_: *mut crate::leanh::LeanObject,
    mut v_a_4034_: *mut crate::leanh::LeanObject,
    mut v_a_4035_: *mut crate::leanh::LeanObject,
    mut v_a_4036_: *mut crate::leanh::LeanObject,
    mut v_a_4037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4043_: u8 = 0;
    let mut v_doc_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v_val_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4064_: u8 = 0;
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_a_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v_ref_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut v_isSharedCheck_4094_: u8 = 0;
    let mut v_a_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4098_: u8 = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4039_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
                if crate::leanh::lean_obj_tag(v___x_4039_) == 0 {
                    v_a_4040_ = crate::leanh::lean_ctor_get(v___x_4039_, 0);
                    v_isSharedCheck_4094_ = (!crate::leanh::lean_is_exclusive(v___x_4039_)) as u8;
                    if v_isSharedCheck_4094_ == 0 {
                        v___x_4042_ = v___x_4039_;
                        v_isShared_4043_ = v_isSharedCheck_4094_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4040_);
                        crate::leanh::lean_dec(v___x_4039_);
                        v___x_4042_ = crate::leanh::lean_box(0);
                        v_isShared_4043_ = v_isSharedCheck_4094_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4095_ = crate::leanh::lean_ctor_get(v___x_4039_, 0);
                    v_isSharedCheck_4102_ = (!crate::leanh::lean_is_exclusive(v___x_4039_)) as u8;
                    if v_isSharedCheck_4102_ == 0 {
                        v___x_4097_ = v___x_4039_;
                        v_isShared_4098_ = v_isSharedCheck_4102_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4095_);
                        crate::leanh::lean_dec(v___x_4039_);
                        v___x_4097_ = crate::leanh::lean_box(0);
                        v_isShared_4098_ = v_isSharedCheck_4102_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4040_) == 0 {
                    v_doc_4044_ = crate::leanh::lean_ctor_get(v_a_4033_, 0);
                    v_uri_4045_ = crate::leanh::lean_ctor_get(v_doc_4044_, 0);
                    v_mod_4046_ = crate::leanh::lean_ctor_get(v_doc_4044_, 1);
                    crate::leanh::lean_inc_ref(v_uri_4045_);
                    crate::leanh::lean_inc(v_mod_4046_);
                    v___x_4047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4047_, 0, v_mod_4046_);
                    crate::leanh::lean_ctor_set(v___x_4047_, 1, v_uri_4045_);
                    v___x_4048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4048_, 0, v___x_4047_);
                    if v_isShared_4043_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4042_, 0, v___x_4048_);
                        v___x_4050_ = v___x_4042_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4051_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4048_);
                        v___x_4050_ = v_reuseFailAlloc_4051_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4042_);
                    v_val_4052_ = crate::leanh::lean_ctor_get(v_a_4040_, 0);
                    v_isSharedCheck_4093_ = (!crate::leanh::lean_is_exclusive(v_a_4040_)) as u8;
                    if v_isSharedCheck_4093_ == 0 {
                        v___x_4054_ = v_a_4040_;
                        v_isShared_4055_ = v_isSharedCheck_4093_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4052_);
                        crate::leanh::lean_dec(v_a_4040_);
                        v___x_4054_ = crate::leanh::lean_box(0);
                        v_isShared_4055_ = v_isSharedCheck_4093_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4050_;
            }
            3 => {
                crate::leanh::lean_inc(v_val_4052_);
                v___x_4056_ = l_Lean_Server_documentUriFromModule_x3f(v_val_4052_);
                if crate::leanh::lean_obj_tag(v___x_4056_) == 0 {
                    crate::leanh::lean_del_object(v___x_4054_);
                    v_a_4057_ = crate::leanh::lean_ctor_get(v___x_4056_, 0);
                    v_isSharedCheck_4077_ = (!crate::leanh::lean_is_exclusive(v___x_4056_)) as u8;
                    if v_isSharedCheck_4077_ == 0 {
                        v___x_4059_ = v___x_4056_;
                        v_isShared_4060_ = v_isSharedCheck_4077_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4057_);
                        crate::leanh::lean_dec(v___x_4056_);
                        v___x_4059_ = crate::leanh::lean_box(0);
                        v_isShared_4060_ = v_isSharedCheck_4077_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_4052_);
                    v_a_4078_ = crate::leanh::lean_ctor_get(v___x_4056_, 0);
                    v_isSharedCheck_4092_ = (!crate::leanh::lean_is_exclusive(v___x_4056_)) as u8;
                    if v_isSharedCheck_4092_ == 0 {
                        v___x_4080_ = v___x_4056_;
                        v_isShared_4081_ = v_isSharedCheck_4092_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4078_);
                        crate::leanh::lean_dec(v___x_4056_);
                        v___x_4080_ = crate::leanh::lean_box(0);
                        v_isShared_4081_ = v_isSharedCheck_4092_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4057_) == 1 {
                    v_val_4061_ = crate::leanh::lean_ctor_get(v_a_4057_, 0);
                    v_isSharedCheck_4072_ = (!crate::leanh::lean_is_exclusive(v_a_4057_)) as u8;
                    if v_isSharedCheck_4072_ == 0 {
                        v___x_4063_ = v_a_4057_;
                        v_isShared_4064_ = v_isSharedCheck_4072_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4061_);
                        crate::leanh::lean_dec(v_a_4057_);
                        v___x_4063_ = crate::leanh::lean_box(0);
                        v_isShared_4064_ = v_isSharedCheck_4072_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4057_);
                    crate::leanh::lean_dec(v_val_4052_);
                    v___x_4073_ = crate::leanh::lean_box(0);
                    if v_isShared_4060_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4059_, 0, v___x_4073_);
                        v___x_4075_ = v___x_4059_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
                        v___x_4075_ = v_reuseFailAlloc_4076_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4065_, 0, v_val_4052_);
                crate::leanh::lean_ctor_set(v___x_4065_, 1, v_val_4061_);
                if v_isShared_4064_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4063_, 0, v___x_4065_);
                    v___x_4067_ = v___x_4063_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4065_);
                    v___x_4067_ = v_reuseFailAlloc_4071_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4059_, 0, v___x_4067_);
                    v___x_4069_ = v___x_4059_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4067_);
                    v___x_4069_ = v_reuseFailAlloc_4070_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4069_;
            }
            8 => {
                return v___x_4075_;
            }
            9 => {
                v_ref_4082_ = crate::leanh::lean_ctor_get(v_a_4036_, 5);
                v___x_4083_ = lean_io_error_to_string(v_a_4078_);
                if v_isShared_4055_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4054_, 3);
                    crate::leanh::lean_ctor_set(v___x_4054_, 0, v___x_4083_);
                    v___x_4085_ = v___x_4054_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4083_);
                    v___x_4085_ = v_reuseFailAlloc_4091_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4086_ = l_Lean_MessageData_ofFormat(v___x_4085_);
                crate::leanh::lean_inc(v_ref_4082_);
                v___x_4087_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4087_, 0, v_ref_4082_);
                crate::leanh::lean_ctor_set(v___x_4087_, 1, v___x_4086_);
                if v_isShared_4081_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4080_, 0, v___x_4087_);
                    v___x_4089_ = v___x_4080_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
                    v___x_4089_ = v_reuseFailAlloc_4090_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4089_;
            }
            12 => {
                if v_isShared_4098_ == 0 {
                    v___x_4100_ = v___x_4097_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
                    v___x_4100_ = v_reuseFailAlloc_4101_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f___boxed(
    mut v_declName_4103_: *mut crate::leanh::LeanObject,
    mut v_a_4104_: *mut crate::leanh::LeanObject,
    mut v_a_4105_: *mut crate::leanh::LeanObject,
    mut v_a_4106_: *mut crate::leanh::LeanObject,
    mut v_a_4107_: *mut crate::leanh::LeanObject,
    mut v_a_4108_: *mut crate::leanh::LeanObject,
    mut v_a_4109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4110_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(
        v_declName_4103_,
        v_a_4104_,
        v_a_4105_,
        v_a_4106_,
        v_a_4107_,
        v_a_4108_,
    );
    crate::leanh::lean_dec(v_a_4108_);
    crate::leanh::lean_dec_ref(v_a_4107_);
    crate::leanh::lean_dec(v_a_4106_);
    crate::leanh::lean_dec_ref(v_a_4105_);
    crate::leanh::lean_dec_ref(v_a_4104_);
    return v_res_4110_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4111_: *mut crate::leanh::LeanObject,
    mut v_constName_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4119_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
    return v___x_4119_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4120_: *mut crate::leanh::LeanObject,
    mut v_constName_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4128_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(v_00_u03b1_4120_, v_constName_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
    crate::leanh::lean_dec(v___y_4126_);
    crate::leanh::lean_dec_ref(v___y_4125_);
    crate::leanh::lean_dec(v___y_4124_);
    crate::leanh::lean_dec_ref(v___y_4123_);
    crate::leanh::lean_dec_ref(v___y_4122_);
    return v_res_4128_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_4129_: *mut crate::leanh::LeanObject,
    mut v_ref_4130_: *mut crate::leanh::LeanObject,
    mut v_constName_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4138_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4130_, v_constName_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
    return v___x_4138_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_4139_: *mut crate::leanh::LeanObject,
    mut v_ref_4140_: *mut crate::leanh::LeanObject,
    mut v_constName_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4148_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_4139_, v_ref_4140_, v_constName_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
    crate::leanh::lean_dec(v___y_4146_);
    crate::leanh::lean_dec_ref(v___y_4145_);
    crate::leanh::lean_dec(v___y_4144_);
    crate::leanh::lean_dec_ref(v___y_4143_);
    crate::leanh::lean_dec_ref(v___y_4142_);
    crate::leanh::lean_dec(v_ref_4140_);
    return v_res_4148_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b1_4149_: *mut crate::leanh::LeanObject,
    mut v_ref_4150_: *mut crate::leanh::LeanObject,
    mut v_msg_4151_: *mut crate::leanh::LeanObject,
    mut v_declHint_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
    mut v___y_4155_: *mut crate::leanh::LeanObject,
    mut v___y_4156_: *mut crate::leanh::LeanObject,
    mut v___y_4157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_4150_, v_msg_4151_, v_declHint_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
    return v___x_4159_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_4160_: *mut crate::leanh::LeanObject,
    mut v_ref_4161_: *mut crate::leanh::LeanObject,
    mut v_msg_4162_: *mut crate::leanh::LeanObject,
    mut v_declHint_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
    mut v___y_4165_: *mut crate::leanh::LeanObject,
    mut v___y_4166_: *mut crate::leanh::LeanObject,
    mut v___y_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4170_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_4160_, v_ref_4161_, v_msg_4162_, v_declHint_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
    crate::leanh::lean_dec(v___y_4168_);
    crate::leanh::lean_dec_ref(v___y_4167_);
    crate::leanh::lean_dec(v___y_4166_);
    crate::leanh::lean_dec_ref(v___y_4165_);
    crate::leanh::lean_dec_ref(v___y_4164_);
    crate::leanh::lean_dec(v_ref_4161_);
    return v_res_4170_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(
    mut v_msg_4171_: *mut crate::leanh::LeanObject,
    mut v_declHint_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
    mut v___y_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4179_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_4171_, v_declHint_4172_, v___y_4177_);
    return v___x_4179_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_msg_4180_: *mut crate::leanh::LeanObject,
    mut v_declHint_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_4180_, v_declHint_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
    crate::leanh::lean_dec(v___y_4186_);
    crate::leanh::lean_dec_ref(v___y_4185_);
    crate::leanh::lean_dec(v___y_4184_);
    crate::leanh::lean_dec_ref(v___y_4183_);
    crate::leanh::lean_dec_ref(v___y_4182_);
    return v_res_4188_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b1_4189_: *mut crate::leanh::LeanObject,
    mut v_ref_4190_: *mut crate::leanh::LeanObject,
    mut v_msg_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4198_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_4190_, v_msg_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
    return v___x_4198_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_4199_: *mut crate::leanh::LeanObject,
    mut v_ref_4200_: *mut crate::leanh::LeanObject,
    mut v_msg_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4208_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_4199_, v_ref_4200_, v_msg_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
    crate::leanh::lean_dec(v___y_4206_);
    crate::leanh::lean_dec_ref(v___y_4205_);
    crate::leanh::lean_dec(v___y_4204_);
    crate::leanh::lean_dec_ref(v___y_4203_);
    crate::leanh::lean_dec_ref(v___y_4202_);
    crate::leanh::lean_dec(v_ref_4200_);
    return v_res_4208_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(
    mut v_00_u03b1_4209_: *mut crate::leanh::LeanObject,
    mut v_msg_4210_: *mut crate::leanh::LeanObject,
    mut v___y_4211_: *mut crate::leanh::LeanObject,
    mut v___y_4212_: *mut crate::leanh::LeanObject,
    mut v___y_4213_: *mut crate::leanh::LeanObject,
    mut v___y_4214_: *mut crate::leanh::LeanObject,
    mut v___y_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_4210_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
    return v___x_4217_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_4218_: *mut crate::leanh::LeanObject,
    mut v_msg_4219_: *mut crate::leanh::LeanObject,
    mut v___y_4220_: *mut crate::leanh::LeanObject,
    mut v___y_4221_: *mut crate::leanh::LeanObject,
    mut v___y_4222_: *mut crate::leanh::LeanObject,
    mut v___y_4223_: *mut crate::leanh::LeanObject,
    mut v___y_4224_: *mut crate::leanh::LeanObject,
    mut v___y_4225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4226_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_4218_, v_msg_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
    crate::leanh::lean_dec(v___y_4224_);
    crate::leanh::lean_dec_ref(v___y_4223_);
    crate::leanh::lean_dec(v___y_4222_);
    crate::leanh::lean_dec_ref(v___y_4221_);
    crate::leanh::lean_dec_ref(v___y_4220_);
    return v_res_4226_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(
    mut v_declName_4227_: *mut crate::leanh::LeanObject,
    mut v___y_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = lean_st_ref_get(v___y_4228_);
    v_env_4231_ = crate::leanh::lean_ctor_get(v___x_4230_, 0);
    crate::leanh::lean_inc_ref(v_env_4231_);
    crate::leanh::lean_dec(v___x_4230_);
    v___x_4232_ = l_Lean_isRecCore(v_env_4231_, v_declName_4227_);
    v___x_4233_ = crate::leanh::lean_box((v___x_4232_) as usize);
    v___x_4234_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4234_, 0, v___x_4233_);
    return v___x_4234_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg___boxed(
    mut v_declName_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4238_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_4235_, v___y_4236_);
    crate::leanh::lean_dec(v___y_4236_);
    return v_res_4238_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(
    mut v_declName_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: u8 = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = lean_st_ref_get(v___y_4240_);
    v_env_4243_ = crate::leanh::lean_ctor_get(v___x_4242_, 0);
    crate::leanh::lean_inc_ref(v_env_4243_);
    crate::leanh::lean_dec(v___x_4242_);
    v___x_4244_ = lean_st_ref_get(v___y_4240_);
    v_env_4245_ = crate::leanh::lean_ctor_get(v___x_4244_, 0);
    crate::leanh::lean_inc_ref(v_env_4245_);
    crate::leanh::lean_dec(v___x_4244_);
    v___x_4246_ = l_Lean_declRangeExt;
    v_toEnvExtension_4247_ = crate::leanh::lean_ctor_get(v___x_4246_, 0);
    v_asyncMode_4248_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4247_, 2);
    v___x_4249_ = l_Lean_instInhabitedDeclarationRanges_default;
    v___x_4250_ = 0;
    crate::leanh::lean_inc(v_declName_4239_);
    v___x_4251_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_4249_,
        v___x_4246_,
        v_env_4243_,
        v_declName_4239_,
        v_asyncMode_4248_,
        v___x_4250_,
    );
    if crate::leanh::lean_obj_tag(v___x_4251_) == 0 {
        let mut v___x_4252_: u8 = 0;
        let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4252_ = 1;
        v___x_4253_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
            v___x_4249_,
            v___x_4246_,
            v_env_4245_,
            v_declName_4239_,
            v_asyncMode_4248_,
            v___x_4252_,
        );
        v___x_4254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4254_, 0, v___x_4253_);
        return v___x_4254_;
    } else {
        let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_4245_);
        crate::leanh::lean_dec(v_declName_4239_);
        v___x_4255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4255_, 0, v___x_4251_);
        return v___x_4255_;
    }
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg___boxed(
    mut v_declName_4256_: *mut crate::leanh::LeanObject,
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_4256_, v___y_4257_);
    crate::leanh::lean_dec(v___y_4257_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(
    mut v_declName_4260_: *mut crate::leanh::LeanObject,
    mut v___y_4261_: *mut crate::leanh::LeanObject,
    mut v___y_4262_: *mut crate::leanh::LeanObject,
    mut v___y_4263_: *mut crate::leanh::LeanObject,
    mut v___y_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ranges_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4283_: u8 = 0;
    let mut v___x_4284_: u8 = 0;
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___x_4288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4274_ = lean_st_ref_get(v___y_4265_);
                v_env_4275_ = crate::leanh::lean_ctor_get(v___x_4274_, 0);
                crate::leanh::lean_inc_ref_n(v_env_4275_, 2);
                crate::leanh::lean_dec(v___x_4274_);
                crate::leanh::lean_inc_n(v_declName_4260_, 2);
                v___x_4276_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_4260_, v___y_4265_);
                v_a_4277_ = crate::leanh::lean_ctor_get(v___x_4276_, 0);
                crate::leanh::lean_inc(v_a_4277_);
                crate::leanh::lean_dec_ref(v___x_4276_);
                v___x_4287_ = l_Lean_isAuxRecursor(v_env_4275_, v_declName_4260_);
                if v___x_4287_ == 0 {
                    crate::leanh::lean_inc(v_declName_4260_);
                    v___x_4288_ = l_Lean_isNoConfusion(v_env_4275_, v_declName_4260_);
                    v___y_4283_ = v___x_4288_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_4275_);
                    v___y_4283_ = v___x_4287_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_ranges_4268_) == 0 {
                    v___x_4269_ = l_Lean_builtinDeclRanges;
                    v___x_4270_ = lean_st_ref_get(v___x_4269_);
                    v___x_4271_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4270_, v_declName_4260_);
                    crate::leanh::lean_dec(v_declName_4260_);
                    crate::leanh::lean_dec(v___x_4270_);
                    v___x_4272_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4272_, 0, v___x_4271_);
                    return v___x_4272_;
                } else {
                    crate::leanh::lean_dec(v_declName_4260_);
                    v___x_4273_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4273_, 0, v_ranges_4268_);
                    return v___x_4273_;
                }
            }
            2 => {
                v___x_4279_ = l_Lean_Name_getPrefix(v_declName_4260_);
                v___x_4280_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v___x_4279_, v___y_4265_);
                v_a_4281_ = crate::leanh::lean_ctor_get(v___x_4280_, 0);
                crate::leanh::lean_inc(v_a_4281_);
                crate::leanh::lean_dec_ref(v___x_4280_);
                v_ranges_4268_ = v_a_4281_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_4283_ == 0 {
                    v___x_4284_ = (crate::leanh::lean_unbox(v_a_4277_) as u8);
                    crate::leanh::lean_dec(v_a_4277_);
                    if v___x_4284_ == 0 {
                        crate::leanh::lean_inc(v_declName_4260_);
                        v___x_4285_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_4260_, v___y_4265_);
                        v_a_4286_ = crate::leanh::lean_ctor_get(v___x_4285_, 0);
                        crate::leanh::lean_inc(v_a_4286_);
                        crate::leanh::lean_dec_ref(v___x_4285_);
                        v_ranges_4268_ = v_a_4286_;
                        state = 1;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4277_);
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0___boxed(
    mut v_declName_4289_: *mut crate::leanh::LeanObject,
    mut v___y_4290_: *mut crate::leanh::LeanObject,
    mut v___y_4291_: *mut crate::leanh::LeanObject,
    mut v___y_4292_: *mut crate::leanh::LeanObject,
    mut v___y_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4296_ =
        l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(
            v_declName_4289_,
            v___y_4290_,
            v___y_4291_,
            v___y_4292_,
            v___y_4293_,
            v___y_4294_,
        );
    crate::leanh::lean_dec(v___y_4294_);
    crate::leanh::lean_dec_ref(v___y_4293_);
    crate::leanh::lean_dec(v___y_4292_);
    crate::leanh::lean_dec_ref(v___y_4291_);
    crate::leanh::lean_dec_ref(v___y_4290_);
    return v_res_4296_;
}
pub unsafe fn l_Lean_Server_locationLinksFromDecl(
    mut v_declName_4299_: *mut crate::leanh::LeanObject,
    mut v_a_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
    mut v_a_4302_: *mut crate::leanh::LeanObject,
    mut v_a_4303_: *mut crate::leanh::LeanObject,
    mut v_a_4304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v_val_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v_val_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4328_: u8 = 0;
    let mut v_doc_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_originInfo_x3f_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: u8 = 0;
    let mut v___y_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_selectionRange_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4338_: u8 = 0;
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4364_: u8 = 0;
    let mut v_text_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4370_: u8 = 0;
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut v_a_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut v_a_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4306_ = lean_st_ref_get(v_a_4304_);
                v_env_4307_ = crate::leanh::lean_ctor_get(v___x_4306_, 0);
                crate::leanh::lean_inc_ref(v_env_4307_);
                crate::leanh::lean_dec(v___x_4306_);
                v___x_4308_ = 1;
                crate::leanh::lean_inc(v_declName_4299_);
                v___x_4309_ =
                    l_Lean_Environment_contains(v_env_4307_, v_declName_4299_, v___x_4308_);
                if v___x_4309_ == 0 {
                    crate::leanh::lean_dec(v_declName_4299_);
                    v___x_4310_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v___x_4311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4311_, 0, v___x_4310_);
                    return v___x_4311_;
                } else {
                    crate::leanh::lean_inc(v_declName_4299_);
                    v___x_4312_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
                    if crate::leanh::lean_obj_tag(v___x_4312_) == 0 {
                        v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                        v_isSharedCheck_4389_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                        if v_isSharedCheck_4389_ == 0 {
                            v___x_4315_ = v___x_4312_;
                            v_isShared_4316_ = v_isSharedCheck_4389_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4313_);
                            crate::leanh::lean_dec(v___x_4312_);
                            v___x_4315_ = crate::leanh::lean_box(0);
                            v_isShared_4316_ = v_isSharedCheck_4389_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_4299_);
                        v_a_4390_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                        v_isSharedCheck_4397_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                        if v_isSharedCheck_4397_ == 0 {
                            v___x_4392_ = v___x_4312_;
                            v_isShared_4393_ = v_isSharedCheck_4397_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4390_);
                            crate::leanh::lean_dec(v___x_4312_);
                            v___x_4392_ = crate::leanh::lean_box(0);
                            v_isShared_4393_ = v_isSharedCheck_4397_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4313_) == 1 {
                    crate::leanh::lean_del_object(v___x_4315_);
                    v_val_4317_ = crate::leanh::lean_ctor_get(v_a_4313_, 0);
                    crate::leanh::lean_inc(v_val_4317_);
                    crate::leanh::lean_dec_ref_known(v_a_4313_, 1);
                    v_fst_4318_ = crate::leanh::lean_ctor_get(v_val_4317_, 0);
                    crate::leanh::lean_inc(v_fst_4318_);
                    v_snd_4319_ = crate::leanh::lean_ctor_get(v_val_4317_, 1);
                    crate::leanh::lean_inc(v_snd_4319_);
                    crate::leanh::lean_dec(v_val_4317_);
                    crate::leanh::lean_inc(v_declName_4299_);
                    v___x_4320_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
                    if crate::leanh::lean_obj_tag(v___x_4320_) == 0 {
                        v_a_4321_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                        v_isSharedCheck_4376_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                        if v_isSharedCheck_4376_ == 0 {
                            v___x_4323_ = v___x_4320_;
                            v_isShared_4324_ = v_isSharedCheck_4376_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4321_);
                            crate::leanh::lean_dec(v___x_4320_);
                            v___x_4323_ = crate::leanh::lean_box(0);
                            v_isShared_4324_ = v_isSharedCheck_4376_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_4319_);
                        crate::leanh::lean_dec(v_fst_4318_);
                        crate::leanh::lean_dec(v_declName_4299_);
                        v_a_4377_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                        v_isSharedCheck_4384_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                        if v_isSharedCheck_4384_ == 0 {
                            v___x_4379_ = v___x_4320_;
                            v_isShared_4380_ = v_isSharedCheck_4384_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4377_);
                            crate::leanh::lean_dec(v___x_4320_);
                            v___x_4379_ = crate::leanh::lean_box(0);
                            v_isShared_4380_ = v_isSharedCheck_4384_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4313_);
                    crate::leanh::lean_dec(v_declName_4299_);
                    v___x_4385_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4316_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4315_, 0, v___x_4385_);
                        v___x_4387_ = v___x_4315_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
                        v___x_4387_ = v_reuseFailAlloc_4388_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4321_) == 1 {
                    v_val_4325_ = crate::leanh::lean_ctor_get(v_a_4321_, 0);
                    v_isSharedCheck_4371_ = (!crate::leanh::lean_is_exclusive(v_a_4321_)) as u8;
                    if v_isSharedCheck_4371_ == 0 {
                        v___x_4327_ = v_a_4321_;
                        v_isShared_4328_ = v_isSharedCheck_4371_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4325_);
                        crate::leanh::lean_dec(v_a_4321_);
                        v___x_4327_ = crate::leanh::lean_box(0);
                        v_isShared_4328_ = v_isSharedCheck_4371_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4321_);
                    crate::leanh::lean_dec(v_snd_4319_);
                    crate::leanh::lean_dec(v_fst_4318_);
                    crate::leanh::lean_dec(v_declName_4299_);
                    v___x_4372_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4324_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4372_);
                        v___x_4374_ = v___x_4323_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4375_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4372_);
                        v___x_4374_ = v_reuseFailAlloc_4375_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v_doc_4329_ = crate::leanh::lean_ctor_get(v_a_4300_, 0);
                v_originInfo_x3f_4330_ = crate::leanh::lean_ctor_get(v_a_4300_, 2);
                v___x_4331_ = 0;
                if crate::leanh::lean_obj_tag(v_originInfo_x3f_4330_) == 0 {
                    v___x_4357_ = crate::leanh::lean_box(0);
                    v___y_4333_ = v___x_4357_;
                    state = 4;
                    continue;
                } else {
                    v_val_4358_ = crate::leanh::lean_ctor_get(v_originInfo_x3f_4330_, 0);
                    v___x_4359_ = l_Lean_Elab_Info_range_x3f(v_val_4358_);
                    if crate::leanh::lean_obj_tag(v___x_4359_) == 0 {
                        v___x_4360_ = crate::leanh::lean_box(0);
                        v___y_4333_ = v___x_4360_;
                        state = 4;
                        continue;
                    } else {
                        v_val_4361_ = crate::leanh::lean_ctor_get(v___x_4359_, 0);
                        v_isSharedCheck_4370_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4359_)) as u8;
                        if v_isSharedCheck_4370_ == 0 {
                            v___x_4363_ = v___x_4359_;
                            v_isShared_4364_ = v_isSharedCheck_4370_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4361_);
                            crate::leanh::lean_dec(v___x_4359_);
                            v___x_4363_ = crate::leanh::lean_box(0);
                            v_isShared_4364_ = v_isSharedCheck_4370_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v_range_4334_ = crate::leanh::lean_ctor_get(v_val_4325_, 0);
                v_selectionRange_4335_ = crate::leanh::lean_ctor_get(v_val_4325_, 1);
                v_isSharedCheck_4356_ = (!crate::leanh::lean_is_exclusive(v_val_4325_)) as u8;
                if v_isSharedCheck_4356_ == 0 {
                    v___x_4337_ = v_val_4325_;
                    v_isShared_4338_ = v_isSharedCheck_4356_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_selectionRange_4335_);
                    crate::leanh::lean_inc(v_range_4334_);
                    crate::leanh::lean_dec(v_val_4325_);
                    v___x_4337_ = crate::leanh::lean_box(0);
                    v_isShared_4338_ = v_isSharedCheck_4356_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4339_ = l_Lean_DeclarationRange_toLspRange(v_range_4334_);
                v___x_4340_ = l_Lean_DeclarationRange_toLspRange(v_selectionRange_4335_);
                v___x_4341_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4341_, 0, v___y_4333_);
                crate::leanh::lean_ctor_set(v___x_4341_, 1, v_snd_4319_);
                crate::leanh::lean_ctor_set(v___x_4341_, 2, v___x_4339_);
                crate::leanh::lean_ctor_set(v___x_4341_, 3, v___x_4340_);
                v___x_4342_ = lean_erase_macro_scopes(v_declName_4299_);
                if v_isShared_4338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4337_, 1, v___x_4342_);
                    crate::leanh::lean_ctor_set(v___x_4337_, 0, v_fst_4318_);
                    v___x_4344_ = v___x_4337_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4355_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_fst_4318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 1, v___x_4342_);
                    v___x_4344_ = v_reuseFailAlloc_4355_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4328_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4327_, 0, v___x_4344_);
                    v___x_4346_ = v___x_4327_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4344_);
                    v___x_4346_ = v_reuseFailAlloc_4354_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4347_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4347_, 0, v___x_4341_);
                crate::leanh::lean_ctor_set(v___x_4347_, 1, v___x_4346_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4331_,
                );
                v___x_4348_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4349_ = lean_mk_empty_array_with_capacity(v___x_4348_);
                v___x_4350_ = lean_array_push(v___x_4349_, v___x_4347_);
                if v_isShared_4324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4350_);
                    v___x_4352_ = v___x_4323_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4350_);
                    v___x_4352_ = v_reuseFailAlloc_4353_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4352_;
            }
            9 => {
                v_text_4365_ = crate::leanh::lean_ctor_get(v_doc_4329_, 3);
                crate::leanh::lean_inc_ref(v_text_4365_);
                v___x_4366_ = l_Lean_Syntax_Range_toLspRange(v_text_4365_, v_val_4361_);
                if v_isShared_4364_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4363_, 0, v___x_4366_);
                    v___x_4368_ = v___x_4363_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4366_);
                    v___x_4368_ = v_reuseFailAlloc_4369_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_4333_ = v___x_4368_;
                state = 4;
                continue;
            }
            11 => {
                return v___x_4374_;
            }
            12 => {
                if v_isShared_4380_ == 0 {
                    v___x_4382_ = v___x_4379_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
                    v___x_4382_ = v_reuseFailAlloc_4383_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4382_;
            }
            14 => {
                return v___x_4387_;
            }
            15 => {
                if v_isShared_4393_ == 0 {
                    v___x_4395_ = v___x_4392_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4395_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromDecl___boxed(
    mut v_declName_4398_: *mut crate::leanh::LeanObject,
    mut v_a_4399_: *mut crate::leanh::LeanObject,
    mut v_a_4400_: *mut crate::leanh::LeanObject,
    mut v_a_4401_: *mut crate::leanh::LeanObject,
    mut v_a_4402_: *mut crate::leanh::LeanObject,
    mut v_a_4403_: *mut crate::leanh::LeanObject,
    mut v_a_4404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4405_ = l_Lean_Server_locationLinksFromDecl(
        v_declName_4398_,
        v_a_4399_,
        v_a_4400_,
        v_a_4401_,
        v_a_4402_,
        v_a_4403_,
    );
    crate::leanh::lean_dec(v_a_4403_);
    crate::leanh::lean_dec_ref(v_a_4402_);
    crate::leanh::lean_dec(v_a_4401_);
    crate::leanh::lean_dec_ref(v_a_4400_);
    crate::leanh::lean_dec_ref(v_a_4399_);
    return v_res_4405_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(
    mut v_declName_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
    mut v___y_4408_: *mut crate::leanh::LeanObject,
    mut v___y_4409_: *mut crate::leanh::LeanObject,
    mut v___y_4410_: *mut crate::leanh::LeanObject,
    mut v___y_4411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4413_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_4406_, v___y_4411_);
    return v___x_4413_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___boxed(
    mut v_declName_4414_: *mut crate::leanh::LeanObject,
    mut v___y_4415_: *mut crate::leanh::LeanObject,
    mut v___y_4416_: *mut crate::leanh::LeanObject,
    mut v___y_4417_: *mut crate::leanh::LeanObject,
    mut v___y_4418_: *mut crate::leanh::LeanObject,
    mut v___y_4419_: *mut crate::leanh::LeanObject,
    mut v___y_4420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4421_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(v_declName_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
    crate::leanh::lean_dec(v___y_4419_);
    crate::leanh::lean_dec_ref(v___y_4418_);
    crate::leanh::lean_dec(v___y_4417_);
    crate::leanh::lean_dec_ref(v___y_4416_);
    crate::leanh::lean_dec_ref(v___y_4415_);
    return v_res_4421_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(
    mut v_declName_4422_: *mut crate::leanh::LeanObject,
    mut v___y_4423_: *mut crate::leanh::LeanObject,
    mut v___y_4424_: *mut crate::leanh::LeanObject,
    mut v___y_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4429_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_4422_, v___y_4427_);
    return v___x_4429_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___boxed(
    mut v_declName_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
    mut v___y_4435_: *mut crate::leanh::LeanObject,
    mut v___y_4436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4437_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(v_declName_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
    crate::leanh::lean_dec(v___y_4435_);
    crate::leanh::lean_dec_ref(v___y_4434_);
    crate::leanh::lean_dec(v___y_4433_);
    crate::leanh::lean_dec_ref(v___y_4432_);
    crate::leanh::lean_dec_ref(v___y_4431_);
    return v_res_4437_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(
    mut v_id_4438_: *mut crate::leanh::LeanObject,
    mut v_x_4439_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4439_) == 1 {
        let mut v_i_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_i_4440_ = crate::leanh::lean_ctor_get(v_x_4439_, 0);
        v_expr_4441_ = crate::leanh::lean_ctor_get(v_i_4440_, 3);
        if crate::leanh::lean_obj_tag(v_expr_4441_) == 1 {
            let mut v_isBinder_4442_: u8 = 0;
            v_isBinder_4442_ = crate::leanh::lean_ctor_get_uint8(
                v_i_4440_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            if v_isBinder_4442_ == 1 {
                let mut v_fvarId_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4444_: u8 = 0;
                v_fvarId_4443_ = crate::leanh::lean_ctor_get(v_expr_4441_, 0);
                v___x_4444_ = l_Lean_instBEqFVarId_beq(v_fvarId_4443_, v_id_4438_);
                return v___x_4444_;
            } else {
                let mut v___x_4445_: u8 = 0;
                v___x_4445_ = 0;
                return v___x_4445_;
            }
        } else {
            let mut v___x_4446_: u8 = 0;
            v___x_4446_ = 0;
            return v___x_4446_;
        }
    } else {
        let mut v___x_4447_: u8 = 0;
        v___x_4447_ = 0;
        return v___x_4447_;
    }
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed(
    mut v_id_4448_: *mut crate::leanh::LeanObject,
    mut v_x_4449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4450_: u8 = 0;
    let mut v_r_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4450_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(v_id_4448_, v_x_4449_);
    crate::leanh::lean_dec_ref(v_x_4449_);
    crate::leanh::lean_dec(v_id_4448_);
    v_r_4451_ = crate::leanh::lean_box((v_res_4450_) as usize);
    return v_r_4451_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(
    mut v_id_4452_: *mut crate::leanh::LeanObject,
    mut v_a_4453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_infoTree_x3f_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_infoTree_x3f_4455_ = crate::leanh::lean_ctor_get(v_a_4453_, 1);
    if crate::leanh::lean_obj_tag(v_infoTree_x3f_4455_) == 1 {
        let mut v_val_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4456_ = crate::leanh::lean_ctor_get(v_infoTree_x3f_4455_, 0);
        v___f_4457_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
        crate::leanh::lean_closure_set(v___f_4457_, 0, v_id_4452_);
        crate::leanh::lean_inc(v_val_4456_);
        v___x_4458_ = l_Lean_Elab_InfoTree_findInfo_x3f(v___f_4457_, v_val_4456_);
        v___x_4459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4459_, 0, v___x_4458_);
        return v___x_4459_;
    } else {
        let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_id_4452_);
        v___x_4460_ = crate::leanh::lean_box(0);
        v___x_4461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4461_, 0, v___x_4460_);
        return v___x_4461_;
    }
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___boxed(
    mut v_id_4462_: *mut crate::leanh::LeanObject,
    mut v_a_4463_: *mut crate::leanh::LeanObject,
    mut v_a_4464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4465_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(
            v_id_4462_, v_a_4463_,
        );
    crate::leanh::lean_dec_ref(v_a_4463_);
    return v_res_4465_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(
    mut v_id_4466_: *mut crate::leanh::LeanObject,
    mut v_a_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
    mut v_a_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4473_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(
            v_id_4466_, v_a_4467_,
        );
    return v___x_4473_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___boxed(
    mut v_id_4474_: *mut crate::leanh::LeanObject,
    mut v_a_4475_: *mut crate::leanh::LeanObject,
    mut v_a_4476_: *mut crate::leanh::LeanObject,
    mut v_a_4477_: *mut crate::leanh::LeanObject,
    mut v_a_4478_: *mut crate::leanh::LeanObject,
    mut v_a_4479_: *mut crate::leanh::LeanObject,
    mut v_a_4480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4481_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(
            v_id_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_,
        );
    crate::leanh::lean_dec(v_a_4479_);
    crate::leanh::lean_dec_ref(v_a_4478_);
    crate::leanh::lean_dec(v_a_4477_);
    crate::leanh::lean_dec_ref(v_a_4476_);
    crate::leanh::lean_dec_ref(v_a_4475_);
    return v_res_4481_;
}
pub unsafe fn l_Lean_Server_locationLinksFromBinder___redArg(
    mut v_id_4482_: *mut crate::leanh::LeanObject,
    mut v_a_4483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4489_: u8 = 0;
    let mut v_val_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_originInfo_x3f_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: u8 = 0;
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4485_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_4482_, v_a_4483_);
                v_a_4486_ = crate::leanh::lean_ctor_get(v___x_4485_, 0);
                v_isSharedCheck_4531_ = (!crate::leanh::lean_is_exclusive(v___x_4485_)) as u8;
                if v_isSharedCheck_4531_ == 0 {
                    v___x_4488_ = v___x_4485_;
                    v_isShared_4489_ = v_isSharedCheck_4531_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4486_);
                    crate::leanh::lean_dec(v___x_4485_);
                    v___x_4488_ = crate::leanh::lean_box(0);
                    v_isShared_4489_ = v_isSharedCheck_4531_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4486_) == 1 {
                    v_val_4490_ = crate::leanh::lean_ctor_get(v_a_4486_, 0);
                    crate::leanh::lean_inc(v_val_4490_);
                    crate::leanh::lean_dec_ref_known(v_a_4486_, 1);
                    v___x_4491_ = l_Lean_Elab_Info_range_x3f(v_val_4490_);
                    crate::leanh::lean_dec(v_val_4490_);
                    if crate::leanh::lean_obj_tag(v___x_4491_) == 1 {
                        v_doc_4492_ = crate::leanh::lean_ctor_get(v_a_4483_, 0);
                        v_val_4493_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
                        crate::leanh::lean_inc(v_val_4493_);
                        crate::leanh::lean_dec_ref_known(v___x_4491_, 1);
                        v_originInfo_x3f_4494_ = crate::leanh::lean_ctor_get(v_a_4483_, 2);
                        v_uri_4495_ = crate::leanh::lean_ctor_get(v_doc_4492_, 0);
                        v_text_4496_ = crate::leanh::lean_ctor_get(v_doc_4492_, 3);
                        crate::leanh::lean_inc_ref(v_text_4496_);
                        v___x_4497_ = l_Lean_Syntax_Range_toLspRange(v_text_4496_, v_val_4493_);
                        if crate::leanh::lean_obj_tag(v_originInfo_x3f_4494_) == 0 {
                            v___x_4510_ = crate::leanh::lean_box(0);
                            v___y_4499_ = v___x_4510_;
                            state = 2;
                            continue;
                        } else {
                            v_val_4511_ = crate::leanh::lean_ctor_get(v_originInfo_x3f_4494_, 0);
                            v___x_4512_ = l_Lean_Elab_Info_range_x3f(v_val_4511_);
                            if crate::leanh::lean_obj_tag(v___x_4512_) == 0 {
                                v___x_4513_ = crate::leanh::lean_box(0);
                                v___y_4499_ = v___x_4513_;
                                state = 2;
                                continue;
                            } else {
                                v_val_4514_ = crate::leanh::lean_ctor_get(v___x_4512_, 0);
                                v_isSharedCheck_4522_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4512_)) as u8;
                                if v_isSharedCheck_4522_ == 0 {
                                    v___x_4516_ = v___x_4512_;
                                    v_isShared_4517_ = v_isSharedCheck_4522_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_4514_);
                                    crate::leanh::lean_dec(v___x_4512_);
                                    v___x_4516_ = crate::leanh::lean_box(0);
                                    v_isShared_4517_ = v_isSharedCheck_4522_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4491_);
                        v___x_4523_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        if v_isShared_4489_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4488_, 0, v___x_4523_);
                            v___x_4525_ = v___x_4488_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4526_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4523_);
                            v___x_4525_ = v_reuseFailAlloc_4526_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4486_);
                    v___x_4527_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4489_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4488_, 0, v___x_4527_);
                        v___x_4529_ = v___x_4488_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4527_);
                        v___x_4529_ = v_reuseFailAlloc_4530_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_4497_);
                crate::leanh::lean_inc_ref(v_uri_4495_);
                v___x_4500_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4500_, 0, v___y_4499_);
                crate::leanh::lean_ctor_set(v___x_4500_, 1, v_uri_4495_);
                crate::leanh::lean_ctor_set(v___x_4500_, 2, v___x_4497_);
                crate::leanh::lean_ctor_set(v___x_4500_, 3, v___x_4497_);
                v___x_4501_ = crate::leanh::lean_box(0);
                v___x_4502_ = 0;
                v___x_4503_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4503_, 0, v___x_4500_);
                crate::leanh::lean_ctor_set(v___x_4503_, 1, v___x_4501_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4503_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4502_,
                );
                v___x_4504_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4505_ = lean_mk_empty_array_with_capacity(v___x_4504_);
                v___x_4506_ = lean_array_push(v___x_4505_, v___x_4503_);
                if v_isShared_4489_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4488_, 0, v___x_4506_);
                    v___x_4508_ = v___x_4488_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
                    v___x_4508_ = v_reuseFailAlloc_4509_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4508_;
            }
            4 => {
                crate::leanh::lean_inc_ref(v_text_4496_);
                v___x_4518_ = l_Lean_Syntax_Range_toLspRange(v_text_4496_, v_val_4514_);
                if v_isShared_4517_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4516_, 0, v___x_4518_);
                    v___x_4520_ = v___x_4516_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
                    v___x_4520_ = v_reuseFailAlloc_4521_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_4499_ = v___x_4520_;
                state = 2;
                continue;
            }
            6 => {
                return v___x_4525_;
            }
            7 => {
                return v___x_4529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromBinder___redArg___boxed(
    mut v_id_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
    mut v_a_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4535_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_4532_, v_a_4533_);
    crate::leanh::lean_dec_ref(v_a_4533_);
    return v_res_4535_;
}
pub unsafe fn l_Lean_Server_locationLinksFromBinder(
    mut v_id_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4543_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_4536_, v_a_4537_);
    return v___x_4543_;
}
pub unsafe fn l_Lean_Server_locationLinksFromBinder___boxed(
    mut v_id_4544_: *mut crate::leanh::LeanObject,
    mut v_a_4545_: *mut crate::leanh::LeanObject,
    mut v_a_4546_: *mut crate::leanh::LeanObject,
    mut v_a_4547_: *mut crate::leanh::LeanObject,
    mut v_a_4548_: *mut crate::leanh::LeanObject,
    mut v_a_4549_: *mut crate::leanh::LeanObject,
    mut v_a_4550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4551_ = l_Lean_Server_locationLinksFromBinder(
        v_id_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_,
    );
    crate::leanh::lean_dec(v_a_4549_);
    crate::leanh::lean_dec_ref(v_a_4548_);
    crate::leanh::lean_dec(v_a_4547_);
    crate::leanh::lean_dec_ref(v_a_4546_);
    crate::leanh::lean_dec_ref(v_a_4545_);
    return v_res_4551_;
}
pub unsafe fn l_Lean_Server_locationLinksFromImport___redArg(
    mut v_i_4583_: *mut crate::leanh::LeanObject,
    mut v_a_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: u8 = 0;
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: u8 = 0;
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v_val_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v_text_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4637_: u8 = 0;
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut v_a_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4646_: u8 = 0;
    let mut v_ref_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut v___y_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: u8 = 0;
    let mut v___x_4664_: u8 = 0;
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: u8 = 0;
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: u8 = 0;
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: u8 = 0;
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: u8 = 0;
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: u8 = 0;
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4696_: u8 = 0;
    let mut v_unused_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stx_4599_ = crate::leanh::lean_ctor_get(v_i_4583_, 1);
                v_isSharedCheck_4696_ = (!crate::leanh::lean_is_exclusive(v_i_4583_)) as u8;
                if v_isSharedCheck_4696_ == 0 {
                    v_unused_4697_ = crate::leanh::lean_ctor_get(v_i_4583_, 0);
                    crate::leanh::lean_dec(v_unused_4697_);
                    v___x_4601_ = v_i_4583_;
                    v_isShared_4602_ = v_isSharedCheck_4696_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stx_4599_);
                    crate::leanh::lean_dec(v_i_4583_);
                    v___x_4601_ = crate::leanh::lean_box(0);
                    v_isShared_4602_ = v_isSharedCheck_4696_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v___y_4588_, 2);
                v___x_4591_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4591_, 0, v___y_4590_);
                crate::leanh::lean_ctor_set(v___x_4591_, 1, v___y_4589_);
                crate::leanh::lean_ctor_set(v___x_4591_, 2, v___y_4588_);
                crate::leanh::lean_ctor_set(v___x_4591_, 3, v___y_4588_);
                v___x_4592_ = crate::leanh::lean_box(0);
                v___x_4593_ = 0;
                v___x_4594_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4594_, 0, v___x_4591_);
                crate::leanh::lean_ctor_set(v___x_4594_, 1, v___x_4592_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4594_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4593_,
                );
                v___x_4595_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4596_ = lean_mk_empty_array_with_capacity(v___x_4595_);
                v___x_4597_ = lean_array_push(v___x_4596_, v___x_4594_);
                v___x_4598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4598_, 0, v___x_4597_);
                return v___x_4598_;
            }
            2 => {
                v___x_4603_ = l_Lean_Server_locationLinksFromImport___redArg___closed__4;
                crate::leanh::lean_inc(v_stx_4599_);
                v___x_4604_ = l_Lean_Syntax_isOfKind(v_stx_4599_, v___x_4603_);
                if v___x_4604_ == 0 {
                    crate::leanh::lean_del_object(v___x_4601_);
                    crate::leanh::lean_dec(v_stx_4599_);
                    v___x_4605_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v___x_4606_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4606_, 0, v___x_4605_);
                    return v___x_4606_;
                } else {
                    v___x_4607_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4685_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4607_);
                    v___x_4686_ = l_Lean_Syntax_isNone(v___x_4685_);
                    if v___x_4686_ == 0 {
                        v___x_4687_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_4685_);
                        v___x_4688_ = l_Lean_Syntax_matchesNull(v___x_4685_, v___x_4687_);
                        if v___x_4688_ == 0 {
                            crate::leanh::lean_dec(v___x_4685_);
                            crate::leanh::lean_del_object(v___x_4601_);
                            crate::leanh::lean_dec(v_stx_4599_);
                            v___x_4689_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                            v___x_4690_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4690_, 0, v___x_4689_);
                            return v___x_4690_;
                        } else {
                            v___x_4691_ = l_Lean_Syntax_getArg(v___x_4685_, v___x_4607_);
                            crate::leanh::lean_dec(v___x_4685_);
                            v___x_4692_ =
                                l_Lean_Server_locationLinksFromImport___redArg___closed__12;
                            v___x_4693_ = l_Lean_Syntax_isOfKind(v___x_4691_, v___x_4692_);
                            if v___x_4693_ == 0 {
                                crate::leanh::lean_del_object(v___x_4601_);
                                crate::leanh::lean_dec(v_stx_4599_);
                                v___x_4694_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                                v___x_4695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4695_, 0, v___x_4694_);
                                return v___x_4695_;
                            } else {
                                v___y_4673_ = v_a_4585_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4685_);
                        v___y_4673_ = v_a_4585_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4610_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_4611_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4610_);
                v___x_4612_ = l_Lean_Syntax_matchesNull(v___x_4611_, v___x_4607_);
                if v___x_4612_ == 0 {
                    crate::leanh::lean_del_object(v___x_4601_);
                    crate::leanh::lean_dec(v_stx_4599_);
                    v___x_4613_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v___x_4614_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4614_, 0, v___x_4613_);
                    return v___x_4614_;
                } else {
                    v___x_4615_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4616_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4615_);
                    crate::leanh::lean_dec(v_stx_4599_);
                    v___x_4617_ = l_Lean_TSyntax_getId(v___x_4616_);
                    v___x_4618_ = l_Lean_Server_documentUriFromModule_x3f(v___x_4617_);
                    if crate::leanh::lean_obj_tag(v___x_4618_) == 0 {
                        crate::leanh::lean_del_object(v___x_4601_);
                        v_a_4619_ = crate::leanh::lean_ctor_get(v___x_4618_, 0);
                        v_isSharedCheck_4642_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4618_)) as u8;
                        if v_isSharedCheck_4642_ == 0 {
                            v___x_4621_ = v___x_4618_;
                            v_isShared_4622_ = v_isSharedCheck_4642_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4619_);
                            crate::leanh::lean_dec(v___x_4618_);
                            v___x_4621_ = crate::leanh::lean_box(0);
                            v_isShared_4622_ = v_isSharedCheck_4642_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4616_);
                        v_a_4643_ = crate::leanh::lean_ctor_get(v___x_4618_, 0);
                        v_isSharedCheck_4657_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4618_)) as u8;
                        if v_isSharedCheck_4657_ == 0 {
                            v___x_4645_ = v___x_4618_;
                            v_isShared_4646_ = v_isSharedCheck_4657_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4643_);
                            crate::leanh::lean_dec(v___x_4618_);
                            v___x_4645_ = crate::leanh::lean_box(0);
                            v_isShared_4646_ = v_isSharedCheck_4657_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4619_) == 1 {
                    crate::leanh::lean_del_object(v___x_4621_);
                    v_val_4623_ = crate::leanh::lean_ctor_get(v_a_4619_, 0);
                    crate::leanh::lean_inc(v_val_4623_);
                    crate::leanh::lean_dec_ref_known(v_a_4619_, 1);
                    v___x_4624_ = l_Lean_Server_locationLinksFromImport___redArg___closed__6;
                    v___x_4625_ = l_Lean_Syntax_getRange_x3f(v___x_4616_, v___x_4604_);
                    crate::leanh::lean_dec(v___x_4616_);
                    if crate::leanh::lean_obj_tag(v___x_4625_) == 0 {
                        v___x_4626_ = crate::leanh::lean_box(0);
                        v___y_4588_ = v___x_4624_;
                        v___y_4589_ = v_val_4623_;
                        v___y_4590_ = v___x_4626_;
                        state = 1;
                        continue;
                    } else {
                        v_doc_4627_ = crate::leanh::lean_ctor_get(v_a_4584_, 0);
                        v_val_4628_ = crate::leanh::lean_ctor_get(v___x_4625_, 0);
                        v_isSharedCheck_4637_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4625_)) as u8;
                        if v_isSharedCheck_4637_ == 0 {
                            v___x_4630_ = v___x_4625_;
                            v_isShared_4631_ = v_isSharedCheck_4637_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4628_);
                            crate::leanh::lean_dec(v___x_4625_);
                            v___x_4630_ = crate::leanh::lean_box(0);
                            v_isShared_4631_ = v_isSharedCheck_4637_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4619_);
                    crate::leanh::lean_dec(v___x_4616_);
                    v___x_4638_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4622_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4621_, 0, v___x_4638_);
                        v___x_4640_ = v___x_4621_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4641_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
                        v___x_4640_ = v_reuseFailAlloc_4641_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v_text_4632_ = crate::leanh::lean_ctor_get(v_doc_4627_, 3);
                crate::leanh::lean_inc_ref(v_text_4632_);
                v___x_4633_ = l_Lean_Syntax_Range_toLspRange(v_text_4632_, v_val_4628_);
                if v_isShared_4631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4630_, 0, v___x_4633_);
                    v___x_4635_ = v___x_4630_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
                    v___x_4635_ = v_reuseFailAlloc_4636_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_4588_ = v___x_4624_;
                v___y_4589_ = v_val_4623_;
                v___y_4590_ = v___x_4635_;
                state = 1;
                continue;
            }
            7 => {
                return v___x_4640_;
            }
            8 => {
                v_ref_4647_ = crate::leanh::lean_ctor_get(v___y_4609_, 5);
                v___x_4648_ = lean_io_error_to_string(v_a_4643_);
                v___x_4649_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4649_, 0, v___x_4648_);
                v___x_4650_ = l_Lean_MessageData_ofFormat(v___x_4649_);
                crate::leanh::lean_inc(v_ref_4647_);
                if v_isShared_4602_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4601_, 1, v___x_4650_);
                    crate::leanh::lean_ctor_set(v___x_4601_, 0, v_ref_4647_);
                    v___x_4652_ = v___x_4601_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_ref_4647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 1, v___x_4650_);
                    v___x_4652_ = v_reuseFailAlloc_4656_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4646_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4645_, 0, v___x_4652_);
                    v___x_4654_ = v___x_4645_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
                    v___x_4654_ = v_reuseFailAlloc_4655_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4654_;
            }
            11 => {
                v___x_4661_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4662_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4661_);
                v___x_4663_ = l_Lean_Syntax_isNone(v___x_4662_);
                if v___x_4663_ == 0 {
                    crate::leanh::lean_inc(v___x_4662_);
                    v___x_4664_ = l_Lean_Syntax_matchesNull(v___x_4662_, v___y_4659_);
                    if v___x_4664_ == 0 {
                        crate::leanh::lean_dec(v___x_4662_);
                        crate::leanh::lean_del_object(v___x_4601_);
                        crate::leanh::lean_dec(v_stx_4599_);
                        v___x_4665_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        v___x_4666_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4666_, 0, v___x_4665_);
                        return v___x_4666_;
                    } else {
                        v___x_4667_ = l_Lean_Syntax_getArg(v___x_4662_, v___x_4607_);
                        crate::leanh::lean_dec(v___x_4662_);
                        v___x_4668_ = l_Lean_Server_locationLinksFromImport___redArg___closed__8;
                        v___x_4669_ = l_Lean_Syntax_isOfKind(v___x_4667_, v___x_4668_);
                        if v___x_4669_ == 0 {
                            crate::leanh::lean_del_object(v___x_4601_);
                            crate::leanh::lean_dec(v_stx_4599_);
                            v___x_4670_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                            v___x_4671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4671_, 0, v___x_4670_);
                            return v___x_4671_;
                        } else {
                            v___y_4609_ = v___y_4660_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4662_);
                    v___y_4609_ = v___y_4660_;
                    state = 3;
                    continue;
                }
            }
            12 => {
                v___x_4674_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4675_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4674_);
                v___x_4676_ = l_Lean_Syntax_isNone(v___x_4675_);
                if v___x_4676_ == 0 {
                    crate::leanh::lean_inc(v___x_4675_);
                    v___x_4677_ = l_Lean_Syntax_matchesNull(v___x_4675_, v___x_4674_);
                    if v___x_4677_ == 0 {
                        crate::leanh::lean_dec(v___x_4675_);
                        crate::leanh::lean_del_object(v___x_4601_);
                        crate::leanh::lean_dec(v_stx_4599_);
                        v___x_4678_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        v___x_4679_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4679_, 0, v___x_4678_);
                        return v___x_4679_;
                    } else {
                        v___x_4680_ = l_Lean_Syntax_getArg(v___x_4675_, v___x_4607_);
                        crate::leanh::lean_dec(v___x_4675_);
                        v___x_4681_ = l_Lean_Server_locationLinksFromImport___redArg___closed__10;
                        v___x_4682_ = l_Lean_Syntax_isOfKind(v___x_4680_, v___x_4681_);
                        if v___x_4682_ == 0 {
                            crate::leanh::lean_del_object(v___x_4601_);
                            crate::leanh::lean_dec(v_stx_4599_);
                            v___x_4683_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                            v___x_4684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4684_, 0, v___x_4683_);
                            return v___x_4684_;
                        } else {
                            v___y_4659_ = v___x_4674_;
                            v___y_4660_ = v___y_4673_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4675_);
                    v___y_4659_ = v___x_4674_;
                    v___y_4660_ = v___y_4673_;
                    state = 11;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromImport___redArg___boxed(
    mut v_i_4698_: *mut crate::leanh::LeanObject,
    mut v_a_4699_: *mut crate::leanh::LeanObject,
    mut v_a_4700_: *mut crate::leanh::LeanObject,
    mut v_a_4701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4702_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_4698_, v_a_4699_, v_a_4700_);
    crate::leanh::lean_dec_ref(v_a_4700_);
    crate::leanh::lean_dec_ref(v_a_4699_);
    return v_res_4702_;
}
pub unsafe fn l_Lean_Server_locationLinksFromImport(
    mut v_i_4703_: *mut crate::leanh::LeanObject,
    mut v_a_4704_: *mut crate::leanh::LeanObject,
    mut v_a_4705_: *mut crate::leanh::LeanObject,
    mut v_a_4706_: *mut crate::leanh::LeanObject,
    mut v_a_4707_: *mut crate::leanh::LeanObject,
    mut v_a_4708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4710_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_4703_, v_a_4704_, v_a_4707_);
    return v___x_4710_;
}
pub unsafe fn l_Lean_Server_locationLinksFromImport___boxed(
    mut v_i_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
    mut v_a_4714_: *mut crate::leanh::LeanObject,
    mut v_a_4715_: *mut crate::leanh::LeanObject,
    mut v_a_4716_: *mut crate::leanh::LeanObject,
    mut v_a_4717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4718_ = l_Lean_Server_locationLinksFromImport(
        v_i_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_,
    );
    crate::leanh::lean_dec(v_a_4716_);
    crate::leanh::lean_dec_ref(v_a_4715_);
    crate::leanh::lean_dec(v_a_4714_);
    crate::leanh::lean_dec_ref(v_a_4713_);
    crate::leanh::lean_dec_ref(v_a_4712_);
    return v_res_4718_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(
    mut v_a_4738_: *mut crate::leanh::LeanObject,
    mut v_a_4739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_originInfo_x3f_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4746_: u8 = 0;
    let mut v_val_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4752_: u8 = 0;
    let mut v_elaborator_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4757_: u8 = 0;
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: u8 = 0;
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: u8 = 0;
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: u8 = 0;
    let mut v_env_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: u8 = 0;
    let mut v_names_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: u8 = 0;
    let mut v___x_4777_: u8 = 0;
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: u8 = 0;
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4785_: u8 = 0;
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4741_ = lean_st_ref_get(v_a_4739_);
                v_originInfo_x3f_4745_ = crate::leanh::lean_ctor_get(v_a_4738_, 2);
                if crate::leanh::lean_obj_tag(v_originInfo_x3f_4745_) == 1 {
                    v_kind_4746_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4738_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_val_4747_ = crate::leanh::lean_ctor_get(v_originInfo_x3f_4745_, 0);
                    crate::leanh::lean_inc(v_val_4747_);
                    v___x_4748_ = l_Lean_Elab_Info_toElabInfo_x3f(v_val_4747_);
                    if crate::leanh::lean_obj_tag(v___x_4748_) == 1 {
                        v_val_4749_ = crate::leanh::lean_ctor_get(v___x_4748_, 0);
                        v_isSharedCheck_4785_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4748_)) as u8;
                        if v_isSharedCheck_4785_ == 0 {
                            v___x_4751_ = v___x_4748_;
                            v_isShared_4752_ = v_isSharedCheck_4785_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4749_);
                            crate::leanh::lean_dec(v___x_4748_);
                            v___x_4751_ = crate::leanh::lean_box(0);
                            v_isShared_4752_ = v_isSharedCheck_4785_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4748_);
                        crate::leanh::lean_dec(v___x_4741_);
                        v___x_4786_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                        v___x_4787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4787_, 0, v___x_4786_);
                        return v___x_4787_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4741_);
                    v___x_4788_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                    v___x_4789_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4789_, 0, v___x_4788_);
                    return v___x_4789_;
                }
            }
            1 => {
                v___x_4743_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                v___x_4744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4744_, 0, v___x_4743_);
                return v___x_4744_;
            }
            2 => {
                v_elaborator_4753_ = crate::leanh::lean_ctor_get(v_val_4749_, 0);
                crate::leanh::lean_inc(v_elaborator_4753_);
                v_stx_4754_ = crate::leanh::lean_ctor_get(v_val_4749_, 1);
                crate::leanh::lean_inc(v_stx_4754_);
                crate::leanh::lean_dec(v_val_4749_);
                v___x_4766_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2;
                v___x_4767_ = lean_name_eq(v_elaborator_4753_, v___x_4766_);
                if v___x_4767_ == 0 {
                    v___x_4768_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6;
                    v___x_4769_ = lean_name_eq(v_elaborator_4753_, v___x_4768_);
                    if v___x_4769_ == 0 {
                        v___x_4770_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8;
                        v___x_4771_ = lean_name_eq(v_elaborator_4753_, v___x_4770_);
                        if v___x_4771_ == 0 {
                            v_env_4772_ = crate::leanh::lean_ctor_get(v___x_4741_, 0);
                            crate::leanh::lean_inc_ref_n(v_env_4772_, 2);
                            crate::leanh::lean_dec(v___x_4741_);
                            v___x_4773_ = 1;
                            v___x_4780_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                            crate::leanh::lean_inc(v_elaborator_4753_);
                            v___x_4781_ = l_Lean_Environment_contains(
                                v_env_4772_,
                                v_elaborator_4753_,
                                v___x_4773_,
                            );
                            if v___x_4781_ == 0 {
                                crate::leanh::lean_dec(v_elaborator_4753_);
                                v_names_4775_ = v___x_4780_;
                                state = 6;
                                continue;
                            } else {
                                v___x_4782_ = lean_array_push(v___x_4780_, v_elaborator_4753_);
                                v_names_4775_ = v___x_4782_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_stx_4754_);
                            crate::leanh::lean_dec(v_elaborator_4753_);
                            crate::leanh::lean_del_object(v___x_4751_);
                            crate::leanh::lean_dec(v___x_4741_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_stx_4754_);
                        crate::leanh::lean_dec(v_elaborator_4753_);
                        crate::leanh::lean_del_object(v___x_4751_);
                        crate::leanh::lean_dec(v___x_4741_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_4754_);
                    crate::leanh::lean_dec(v_elaborator_4753_);
                    crate::leanh::lean_del_object(v___x_4751_);
                    crate::leanh::lean_dec(v___x_4741_);
                    v___x_4783_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                    v___x_4784_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4784_, 0, v___x_4783_);
                    return v___x_4784_;
                }
            }
            3 => {
                if v___y_4757_ == 0 {
                    crate::leanh::lean_dec(v_stx_4754_);
                    if v_isShared_4752_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4751_, 0);
                        crate::leanh::lean_ctor_set(v___x_4751_, 0, v___y_4756_);
                        v___x_4759_ = v___x_4751_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4760_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___y_4756_);
                        v___x_4759_ = v_reuseFailAlloc_4760_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_4761_ = l_Lean_Syntax_getKind(v_stx_4754_);
                    v___x_4762_ = lean_array_push(v___y_4756_, v___x_4761_);
                    if v_isShared_4752_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4751_, 0);
                        crate::leanh::lean_ctor_set(v___x_4751_, 0, v___x_4762_);
                        v___x_4764_ = v___x_4751_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
                        v___x_4764_ = v_reuseFailAlloc_4765_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4759_;
            }
            5 => {
                return v___x_4764_;
            }
            6 => {
                v___x_4776_ = 0;
                v___x_4777_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_4746_, v___x_4776_);
                if v___x_4777_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_4772_);
                    v___y_4756_ = v_names_4775_;
                    v___y_4757_ = v___x_4777_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stx_4754_);
                    v___x_4778_ = l_Lean_Syntax_getKind(v_stx_4754_);
                    v___x_4779_ =
                        l_Lean_Environment_contains(v_env_4772_, v___x_4778_, v___x_4773_);
                    v___y_4756_ = v_names_4775_;
                    v___y_4757_ = v___x_4779_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___boxed(
    mut v_a_4790_: *mut crate::leanh::LeanObject,
    mut v_a_4791_: *mut crate::leanh::LeanObject,
    mut v_a_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4793_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(
            v_a_4790_, v_a_4791_,
        );
    crate::leanh::lean_dec(v_a_4791_);
    crate::leanh::lean_dec_ref(v_a_4790_);
    return v_res_4793_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(
    mut v_a_4794_: *mut crate::leanh::LeanObject,
    mut v_a_4795_: *mut crate::leanh::LeanObject,
    mut v_a_4796_: *mut crate::leanh::LeanObject,
    mut v_a_4797_: *mut crate::leanh::LeanObject,
    mut v_a_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(
            v_a_4794_, v_a_4798_,
        );
    return v___x_4800_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___boxed(
    mut v_a_4801_: *mut crate::leanh::LeanObject,
    mut v_a_4802_: *mut crate::leanh::LeanObject,
    mut v_a_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4807_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(
        v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_,
    );
    crate::leanh::lean_dec(v_a_4805_);
    crate::leanh::lean_dec_ref(v_a_4804_);
    crate::leanh::lean_dec(v_a_4803_);
    crate::leanh::lean_dec_ref(v_a_4802_);
    crate::leanh::lean_dec_ref(v_a_4801_);
    return v_res_4807_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(
    mut v_as_4808_: *mut crate::leanh::LeanObject,
    mut v_sz_4809_: usize,
    mut v_i_4810_: usize,
    mut v_b_4811_: *mut crate::leanh::LeanObject,
    mut v___y_4812_: *mut crate::leanh::LeanObject,
    mut v___y_4813_: *mut crate::leanh::LeanObject,
    mut v___y_4814_: *mut crate::leanh::LeanObject,
    mut v___y_4815_: *mut crate::leanh::LeanObject,
    mut v___y_4816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: u8 = 0;
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: usize = 0;
    let mut v___x_4825_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4818_ = lean_usize_dec_lt(v_i_4810_, v_sz_4809_);
                if v___x_4818_ == 0 {
                    v___x_4819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4819_, 0, v_b_4811_);
                    return v___x_4819_;
                } else {
                    v_a_4820_ = lean_array_uget_borrowed(v_as_4808_, v_i_4810_);
                    crate::leanh::lean_inc(v_a_4820_);
                    v___x_4821_ = l_Lean_Server_locationLinksFromDecl(
                        v_a_4820_,
                        v___y_4812_,
                        v___y_4813_,
                        v___y_4814_,
                        v___y_4815_,
                        v___y_4816_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4821_) == 0 {
                        v_a_4822_ = crate::leanh::lean_ctor_get(v___x_4821_, 0);
                        crate::leanh::lean_inc(v_a_4822_);
                        crate::leanh::lean_dec_ref_known(v___x_4821_, 1);
                        v___x_4823_ = l_Array_append___redArg(v_b_4811_, v_a_4822_);
                        crate::leanh::lean_dec(v_a_4822_);
                        v___x_4824_ = 1usize;
                        v___x_4825_ = lean_usize_add(v_i_4810_, v___x_4824_);
                        v_i_4810_ = v___x_4825_;
                        v_b_4811_ = v___x_4823_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4811_);
                        return v___x_4821_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0___boxed(
    mut v_as_4827_: *mut crate::leanh::LeanObject,
    mut v_sz_4828_: *mut crate::leanh::LeanObject,
    mut v_i_4829_: *mut crate::leanh::LeanObject,
    mut v_b_4830_: *mut crate::leanh::LeanObject,
    mut v___y_4831_: *mut crate::leanh::LeanObject,
    mut v___y_4832_: *mut crate::leanh::LeanObject,
    mut v___y_4833_: *mut crate::leanh::LeanObject,
    mut v___y_4834_: *mut crate::leanh::LeanObject,
    mut v___y_4835_: *mut crate::leanh::LeanObject,
    mut v___y_4836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4837_: usize = 0;
    let mut v_i_boxed_4838_: usize = 0;
    let mut v_res_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4837_ = crate::leanh::lean_unbox_usize(v_sz_4828_);
    crate::leanh::lean_dec(v_sz_4828_);
    v_i_boxed_4838_ = crate::leanh::lean_unbox_usize(v_i_4829_);
    crate::leanh::lean_dec(v_i_4829_);
    v_res_4839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_as_4827_, v_sz_boxed_4837_, v_i_boxed_4838_, v_b_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
    crate::leanh::lean_dec(v___y_4835_);
    crate::leanh::lean_dec_ref(v___y_4834_);
    crate::leanh::lean_dec(v___y_4833_);
    crate::leanh::lean_dec_ref(v___y_4832_);
    crate::leanh::lean_dec_ref(v___y_4831_);
    crate::leanh::lean_dec_ref(v_as_4827_);
    return v_res_4839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(
    mut v_sz_4840_: usize,
    mut v_i_4841_: usize,
    mut v_bs_4842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4843_: u8 = 0;
    let mut v_v_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLocationLink_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ident_x3f_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4849_: u8 = 0;
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: usize = 0;
    let mut v___x_4855_: usize = 0;
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4843_ = lean_usize_dec_lt(v_i_4841_, v_sz_4840_);
                if v___x_4843_ == 0 {
                    return v_bs_4842_;
                } else {
                    v_v_4844_ = lean_array_uget(v_bs_4842_, v_i_4841_);
                    v_toLocationLink_4845_ = crate::leanh::lean_ctor_get(v_v_4844_, 0);
                    v_ident_x3f_4846_ = crate::leanh::lean_ctor_get(v_v_4844_, 1);
                    v_isSharedCheck_4859_ = (!crate::leanh::lean_is_exclusive(v_v_4844_)) as u8;
                    if v_isSharedCheck_4859_ == 0 {
                        v___x_4848_ = v_v_4844_;
                        v_isShared_4849_ = v_isSharedCheck_4859_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_ident_x3f_4846_);
                        crate::leanh::lean_inc(v_toLocationLink_4845_);
                        crate::leanh::lean_dec(v_v_4844_);
                        v___x_4848_ = crate::leanh::lean_box(0);
                        v_isShared_4849_ = v_isSharedCheck_4859_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4850_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_4851_ = lean_array_uset(v_bs_4842_, v_i_4841_, v___x_4850_);
                if v_isShared_4849_ == 0 {
                    v___x_4853_ = v___x_4848_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_toLocationLink_4845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_ident_x3f_4846_);
                    v___x_4853_ = v_reuseFailAlloc_4858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4853_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4843_,
                );
                v___x_4854_ = 1usize;
                v___x_4855_ = lean_usize_add(v_i_4841_, v___x_4854_);
                v___x_4856_ = lean_array_uset(v_bs_x27_4851_, v_i_4841_, v___x_4853_);
                v_i_4841_ = v___x_4855_;
                v_bs_4842_ = v___x_4856_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1___boxed(
    mut v_sz_4860_: *mut crate::leanh::LeanObject,
    mut v_i_4861_: *mut crate::leanh::LeanObject,
    mut v_bs_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4863_: usize = 0;
    let mut v_i_boxed_4864_: usize = 0;
    let mut v_res_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4863_ = crate::leanh::lean_unbox_usize(v_sz_4860_);
    crate::leanh::lean_dec(v_sz_4860_);
    v_i_boxed_4864_ = crate::leanh::lean_unbox_usize(v_i_4861_);
    crate::leanh::lean_dec(v_i_4861_);
    v_res_4865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_boxed_4863_, v_i_boxed_4864_, v_bs_4862_);
    return v_res_4865_;
}
pub unsafe fn l_Lean_Server_locationLinksDefault(
    mut v_a_4866_: *mut crate::leanh::LeanObject,
    mut v_a_4867_: *mut crate::leanh::LeanObject,
    mut v_a_4868_: *mut crate::leanh::LeanObject,
    mut v_a_4869_: *mut crate::leanh::LeanObject,
    mut v_a_4870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4875_: usize = 0;
    let mut v___x_4876_: usize = 0;
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v_sz_4882_: usize = 0;
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4872_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_4866_, v_a_4870_);
                v_a_4873_ = crate::leanh::lean_ctor_get(v___x_4872_, 0);
                crate::leanh::lean_inc(v_a_4873_);
                crate::leanh::lean_dec_ref(v___x_4872_);
                v___x_4874_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                v_sz_4875_ = lean_array_size(v_a_4873_);
                v___x_4876_ = 0usize;
                v___x_4877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_4873_, v_sz_4875_, v___x_4876_, v___x_4874_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
                crate::leanh::lean_dec(v_a_4873_);
                if crate::leanh::lean_obj_tag(v___x_4877_) == 0 {
                    v_a_4878_ = crate::leanh::lean_ctor_get(v___x_4877_, 0);
                    v_isSharedCheck_4887_ = (!crate::leanh::lean_is_exclusive(v___x_4877_)) as u8;
                    if v_isSharedCheck_4887_ == 0 {
                        v___x_4880_ = v___x_4877_;
                        v_isShared_4881_ = v_isSharedCheck_4887_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4878_);
                        crate::leanh::lean_dec(v___x_4877_);
                        v___x_4880_ = crate::leanh::lean_box(0);
                        v_isShared_4881_ = v_isSharedCheck_4887_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4877_;
                }
            }
            1 => {
                v_sz_4882_ = lean_array_size(v_a_4878_);
                v___x_4883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_4882_, v___x_4876_, v_a_4878_);
                if v_isShared_4881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_4883_);
                    v___x_4885_ = v___x_4880_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
                    v___x_4885_ = v_reuseFailAlloc_4886_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4885_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksDefault___boxed(
    mut v_a_4888_: *mut crate::leanh::LeanObject,
    mut v_a_4889_: *mut crate::leanh::LeanObject,
    mut v_a_4890_: *mut crate::leanh::LeanObject,
    mut v_a_4891_: *mut crate::leanh::LeanObject,
    mut v_a_4892_: *mut crate::leanh::LeanObject,
    mut v_a_4893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4894_ =
        l_Lean_Server_locationLinksDefault(v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_);
    crate::leanh::lean_dec(v_a_4892_);
    crate::leanh::lean_dec_ref(v_a_4891_);
    crate::leanh::lean_dec(v_a_4890_);
    crate::leanh::lean_dec_ref(v_a_4889_);
    crate::leanh::lean_dec_ref(v_a_4888_);
    return v_res_4894_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(
    mut v_name_4895_: *mut crate::leanh::LeanObject,
    mut v___y_4896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4898_ = lean_st_ref_get(v___y_4896_);
    v_env_4899_ = crate::leanh::lean_ctor_get(v___x_4898_, 0);
    crate::leanh::lean_inc_ref(v_env_4899_);
    crate::leanh::lean_dec(v___x_4898_);
    v___x_4900_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_4901_ = crate::leanh::lean_ctor_get(v___x_4900_, 0);
    v_asyncMode_4902_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4901_, 2);
    v___x_4903_ = crate::leanh::lean_box(1);
    v___x_4904_ = crate::leanh::lean_box(0);
    v___x_4905_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_4903_,
        v___x_4900_,
        v_env_4899_,
        v_asyncMode_4902_,
        v___x_4904_,
    );
    v___x_4906_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_4905_,
            v_name_4895_,
        );
    crate::leanh::lean_dec(v___x_4905_);
    v___x_4907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4907_, 0, v___x_4906_);
    return v___x_4907_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg___boxed(
    mut v_name_4908_: *mut crate::leanh::LeanObject,
    mut v___y_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4911_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_4908_, v___y_4909_);
    crate::leanh::lean_dec(v___y_4909_);
    crate::leanh::lean_dec(v_name_4908_);
    return v_res_4911_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(
    mut v_name_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
    mut v___y_4915_: *mut crate::leanh::LeanObject,
    mut v___y_4916_: *mut crate::leanh::LeanObject,
    mut v___y_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4919_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_4912_, v___y_4917_);
    return v___x_4919_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___boxed(
    mut v_name_4920_: *mut crate::leanh::LeanObject,
    mut v___y_4921_: *mut crate::leanh::LeanObject,
    mut v___y_4922_: *mut crate::leanh::LeanObject,
    mut v___y_4923_: *mut crate::leanh::LeanObject,
    mut v___y_4924_: *mut crate::leanh::LeanObject,
    mut v___y_4925_: *mut crate::leanh::LeanObject,
    mut v___y_4926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4927_ =
        l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(
            v_name_4920_,
            v___y_4921_,
            v___y_4922_,
            v___y_4923_,
            v___y_4924_,
            v___y_4925_,
        );
    crate::leanh::lean_dec(v___y_4925_);
    crate::leanh::lean_dec_ref(v___y_4924_);
    crate::leanh::lean_dec(v___y_4923_);
    crate::leanh::lean_dec_ref(v___y_4922_);
    crate::leanh::lean_dec_ref(v___y_4921_);
    crate::leanh::lean_dec(v_name_4920_);
    return v_res_4927_;
}
pub unsafe fn l_Lean_Server_locationLinksFromErrorNameInfo(
    mut v_eni_4928_: *mut crate::leanh::LeanObject,
    mut v_a_4929_: *mut crate::leanh::LeanObject,
    mut v_a_4930_: *mut crate::leanh::LeanObject,
    mut v_a_4931_: *mut crate::leanh::LeanObject,
    mut v_a_4932_: *mut crate::leanh::LeanObject,
    mut v_a_4933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stx_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorName_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v_val_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declLoc_x3f_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4947_: u8 = 0;
    let mut v_module_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4952_: u8 = 0;
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4957_: u8 = 0;
    let mut v_val_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: u8 = 0;
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: u8 = 0;
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4979_: u8 = 0;
    let mut v_text_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4985_: u8 = 0;
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4990_: u8 = 0;
    let mut v_a_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4994_: u8 = 0;
    let mut v_ref_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_isSharedCheck_5009_: u8 = 0;
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stx_4935_ = crate::leanh::lean_ctor_get(v_eni_4928_, 0);
                v_errorName_4936_ = crate::leanh::lean_ctor_get(v_eni_4928_, 1);
                v___x_4937_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_errorName_4936_, v_a_4933_);
                v_a_4938_ = crate::leanh::lean_ctor_get(v___x_4937_, 0);
                v_isSharedCheck_5018_ = (!crate::leanh::lean_is_exclusive(v___x_4937_)) as u8;
                if v_isSharedCheck_5018_ == 0 {
                    v___x_4940_ = v___x_4937_;
                    v_isShared_4941_ = v_isSharedCheck_5018_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4938_);
                    crate::leanh::lean_dec(v___x_4937_);
                    v___x_4940_ = crate::leanh::lean_box(0);
                    v_isShared_4941_ = v_isSharedCheck_5018_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4938_) == 1 {
                    v_val_4942_ = crate::leanh::lean_ctor_get(v_a_4938_, 0);
                    crate::leanh::lean_inc(v_val_4942_);
                    crate::leanh::lean_dec_ref_known(v_a_4938_, 1);
                    v_declLoc_x3f_4943_ = crate::leanh::lean_ctor_get(v_val_4942_, 2);
                    crate::leanh::lean_inc(v_declLoc_x3f_4943_);
                    crate::leanh::lean_dec(v_val_4942_);
                    if crate::leanh::lean_obj_tag(v_declLoc_x3f_4943_) == 1 {
                        crate::leanh::lean_del_object(v___x_4940_);
                        v_val_4944_ = crate::leanh::lean_ctor_get(v_declLoc_x3f_4943_, 0);
                        v_isSharedCheck_5009_ =
                            (!crate::leanh::lean_is_exclusive(v_declLoc_x3f_4943_)) as u8;
                        if v_isSharedCheck_5009_ == 0 {
                            v___x_4946_ = v_declLoc_x3f_4943_;
                            v_isShared_4947_ = v_isSharedCheck_5009_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4944_);
                            crate::leanh::lean_dec(v_declLoc_x3f_4943_);
                            v___x_4946_ = crate::leanh::lean_box(0);
                            v_isShared_4947_ = v_isSharedCheck_5009_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declLoc_x3f_4943_);
                        v___x_5010_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        if v_isShared_4941_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4940_, 0, v___x_5010_);
                            v___x_5012_ = v___x_4940_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_5013_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_5010_);
                            v___x_5012_ = v_reuseFailAlloc_5013_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4938_);
                    v___x_5014_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4941_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4940_, 0, v___x_5014_);
                        v___x_5016_ = v___x_4940_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_5017_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_5014_);
                        v___x_5016_ = v_reuseFailAlloc_5017_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_module_4948_ = crate::leanh::lean_ctor_get(v_val_4944_, 0);
                v_range_4949_ = crate::leanh::lean_ctor_get(v_val_4944_, 1);
                v_isSharedCheck_5008_ = (!crate::leanh::lean_is_exclusive(v_val_4944_)) as u8;
                if v_isSharedCheck_5008_ == 0 {
                    v___x_4951_ = v_val_4944_;
                    v_isShared_4952_ = v_isSharedCheck_5008_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_range_4949_);
                    crate::leanh::lean_inc(v_module_4948_);
                    crate::leanh::lean_dec(v_val_4944_);
                    v___x_4951_ = crate::leanh::lean_box(0);
                    v_isShared_4952_ = v_isSharedCheck_5008_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4953_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4948_);
                if crate::leanh::lean_obj_tag(v___x_4953_) == 0 {
                    crate::leanh::lean_del_object(v___x_4951_);
                    crate::leanh::lean_del_object(v___x_4946_);
                    v_a_4954_ = crate::leanh::lean_ctor_get(v___x_4953_, 0);
                    v_isSharedCheck_4990_ = (!crate::leanh::lean_is_exclusive(v___x_4953_)) as u8;
                    if v_isSharedCheck_4990_ == 0 {
                        v___x_4956_ = v___x_4953_;
                        v_isShared_4957_ = v_isSharedCheck_4990_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4954_);
                        crate::leanh::lean_dec(v___x_4953_);
                        v___x_4956_ = crate::leanh::lean_box(0);
                        v_isShared_4957_ = v_isSharedCheck_4990_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_range_4949_);
                    v_a_4991_ = crate::leanh::lean_ctor_get(v___x_4953_, 0);
                    v_isSharedCheck_5007_ = (!crate::leanh::lean_is_exclusive(v___x_4953_)) as u8;
                    if v_isSharedCheck_5007_ == 0 {
                        v___x_4993_ = v___x_4953_;
                        v_isShared_4994_ = v_isSharedCheck_5007_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4991_);
                        crate::leanh::lean_dec(v___x_4953_);
                        v___x_4993_ = crate::leanh::lean_box(0);
                        v_isShared_4994_ = v_isSharedCheck_5007_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4954_) == 1 {
                    v_val_4958_ = crate::leanh::lean_ctor_get(v_a_4954_, 0);
                    crate::leanh::lean_inc(v_val_4958_);
                    crate::leanh::lean_dec_ref_known(v_a_4954_, 1);
                    v___x_4959_ = l_Lean_DeclarationRange_toLspRange(v_range_4949_);
                    v___x_4972_ = 1;
                    v___x_4973_ = l_Lean_Syntax_getRange_x3f(v_stx_4935_, v___x_4972_);
                    if crate::leanh::lean_obj_tag(v___x_4973_) == 0 {
                        v___x_4974_ = crate::leanh::lean_box(0);
                        v___y_4961_ = v___x_4974_;
                        state = 5;
                        continue;
                    } else {
                        v_doc_4975_ = crate::leanh::lean_ctor_get(v_a_4929_, 0);
                        v_val_4976_ = crate::leanh::lean_ctor_get(v___x_4973_, 0);
                        v_isSharedCheck_4985_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4973_)) as u8;
                        if v_isSharedCheck_4985_ == 0 {
                            v___x_4978_ = v___x_4973_;
                            v_isShared_4979_ = v_isSharedCheck_4985_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4976_);
                            crate::leanh::lean_dec(v___x_4973_);
                            v___x_4978_ = crate::leanh::lean_box(0);
                            v_isShared_4979_ = v_isSharedCheck_4985_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4954_);
                    crate::leanh::lean_dec_ref(v_range_4949_);
                    v___x_4986_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4957_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4956_, 0, v___x_4986_);
                        v___x_4988_ = v___x_4956_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4989_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4986_);
                        v___x_4988_ = v_reuseFailAlloc_4989_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_4959_);
                v___x_4962_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4962_, 0, v___y_4961_);
                crate::leanh::lean_ctor_set(v___x_4962_, 1, v_val_4958_);
                crate::leanh::lean_ctor_set(v___x_4962_, 2, v___x_4959_);
                crate::leanh::lean_ctor_set(v___x_4962_, 3, v___x_4959_);
                v___x_4963_ = crate::leanh::lean_box(0);
                v___x_4964_ = 0;
                v___x_4965_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4965_, 0, v___x_4962_);
                crate::leanh::lean_ctor_set(v___x_4965_, 1, v___x_4963_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4965_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4964_,
                );
                v___x_4966_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4967_ = lean_mk_empty_array_with_capacity(v___x_4966_);
                v___x_4968_ = lean_array_push(v___x_4967_, v___x_4965_);
                if v_isShared_4957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4956_, 0, v___x_4968_);
                    v___x_4970_ = v___x_4956_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4971_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4968_);
                    v___x_4970_ = v_reuseFailAlloc_4971_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4970_;
            }
            7 => {
                v_text_4980_ = crate::leanh::lean_ctor_get(v_doc_4975_, 3);
                crate::leanh::lean_inc_ref(v_text_4980_);
                v___x_4981_ = l_Lean_Syntax_Range_toLspRange(v_text_4980_, v_val_4976_);
                if v_isShared_4979_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4978_, 0, v___x_4981_);
                    v___x_4983_ = v___x_4978_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4984_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4984_, 0, v___x_4981_);
                    v___x_4983_ = v_reuseFailAlloc_4984_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_4961_ = v___x_4983_;
                state = 5;
                continue;
            }
            9 => {
                return v___x_4988_;
            }
            10 => {
                v_ref_4995_ = crate::leanh::lean_ctor_get(v_a_4932_, 5);
                v___x_4996_ = lean_io_error_to_string(v_a_4991_);
                if v_isShared_4947_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4946_, 3);
                    crate::leanh::lean_ctor_set(v___x_4946_, 0, v___x_4996_);
                    v___x_4998_ = v___x_4946_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_4996_);
                    v___x_4998_ = v_reuseFailAlloc_5006_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4999_ = l_Lean_MessageData_ofFormat(v___x_4998_);
                crate::leanh::lean_inc(v_ref_4995_);
                if v_isShared_4952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4951_, 1, v___x_4999_);
                    crate::leanh::lean_ctor_set(v___x_4951_, 0, v_ref_4995_);
                    v___x_5001_ = v___x_4951_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_ref_4995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 1, v___x_4999_);
                    v___x_5001_ = v_reuseFailAlloc_5005_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4993_, 0, v___x_5001_);
                    v___x_5003_ = v___x_4993_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5001_);
                    v___x_5003_ = v_reuseFailAlloc_5004_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5003_;
            }
            14 => {
                return v___x_5012_;
            }
            15 => {
                return v___x_5016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromErrorNameInfo___boxed(
    mut v_eni_5019_: *mut crate::leanh::LeanObject,
    mut v_a_5020_: *mut crate::leanh::LeanObject,
    mut v_a_5021_: *mut crate::leanh::LeanObject,
    mut v_a_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
    mut v_a_5024_: *mut crate::leanh::LeanObject,
    mut v_a_5025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5026_ = l_Lean_Server_locationLinksFromErrorNameInfo(
        v_eni_5019_,
        v_a_5020_,
        v_a_5021_,
        v_a_5022_,
        v_a_5023_,
        v_a_5024_,
    );
    crate::leanh::lean_dec(v_a_5024_);
    crate::leanh::lean_dec_ref(v_a_5023_);
    crate::leanh::lean_dec(v_a_5022_);
    crate::leanh::lean_dec_ref(v_a_5021_);
    crate::leanh::lean_dec_ref(v_a_5020_);
    crate::leanh::lean_dec_ref(v_eni_5019_);
    return v_res_5026_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(
    mut v_e_5027_: *mut crate::leanh::LeanObject,
    mut v_a_5028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5036_: u8 = 0;
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5047_: u8 = 0;
    let mut v_a_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5055_: u8 = 0;
    let mut v_fn_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5064_: u8 = 0;
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5069_: u8 = 0;
    let mut v_expr_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_5027_) {
                4 => {
                    v_declName_5030_ = crate::leanh::lean_ctor_get(v_e_5027_, 0);
                    crate::leanh::lean_inc(v_declName_5030_);
                    crate::leanh::lean_dec_ref_known(v_e_5027_, 2);
                    v___x_5031_ = l_Lean_Meta_isInstance___redArg(v_declName_5030_, v_a_5028_);
                    if crate::leanh::lean_obj_tag(v___x_5031_) == 0 {
                        v_a_5032_ = crate::leanh::lean_ctor_get(v___x_5031_, 0);
                        v_isSharedCheck_5047_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5031_)) as u8;
                        if v_isSharedCheck_5047_ == 0 {
                            v___x_5034_ = v___x_5031_;
                            v_isShared_5035_ = v_isSharedCheck_5047_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5032_);
                            crate::leanh::lean_dec(v___x_5031_);
                            v___x_5034_ = crate::leanh::lean_box(0);
                            v_isShared_5035_ = v_isSharedCheck_5047_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_5030_);
                        v_a_5048_ = crate::leanh::lean_ctor_get(v___x_5031_, 0);
                        v_isSharedCheck_5055_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5031_)) as u8;
                        if v_isSharedCheck_5055_ == 0 {
                            v___x_5050_ = v___x_5031_;
                            v_isShared_5051_ = v_isSharedCheck_5055_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5048_);
                            crate::leanh::lean_dec(v___x_5031_);
                            v___x_5050_ = crate::leanh::lean_box(0);
                            v_isShared_5051_ = v_isSharedCheck_5055_;
                            state = 4;
                            continue;
                        }
                    }
                }
                5 => {
                    v_fn_5056_ = crate::leanh::lean_ctor_get(v_e_5027_, 0);
                    crate::leanh::lean_inc_ref(v_fn_5056_);
                    v_arg_5057_ = crate::leanh::lean_ctor_get(v_e_5027_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5057_);
                    crate::leanh::lean_dec_ref_known(v_e_5027_, 2);
                    v___x_5058_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_fn_5056_, v_a_5028_);
                    if crate::leanh::lean_obj_tag(v___x_5058_) == 0 {
                        v_a_5059_ = crate::leanh::lean_ctor_get(v___x_5058_, 0);
                        crate::leanh::lean_inc(v_a_5059_);
                        crate::leanh::lean_dec_ref_known(v___x_5058_, 1);
                        v___x_5060_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_arg_5057_, v_a_5028_);
                        if crate::leanh::lean_obj_tag(v___x_5060_) == 0 {
                            v_a_5061_ = crate::leanh::lean_ctor_get(v___x_5060_, 0);
                            v_isSharedCheck_5069_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5060_)) as u8;
                            if v_isSharedCheck_5069_ == 0 {
                                v___x_5063_ = v___x_5060_;
                                v_isShared_5064_ = v_isSharedCheck_5069_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5061_);
                                crate::leanh::lean_dec(v___x_5060_);
                                v___x_5063_ = crate::leanh::lean_box(0);
                                v_isShared_5064_ = v_isSharedCheck_5069_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5059_);
                            return v___x_5060_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_5057_);
                        return v___x_5058_;
                    }
                }
                10 => {
                    v_expr_5070_ = crate::leanh::lean_ctor_get(v_e_5027_, 1);
                    crate::leanh::lean_inc_ref(v_expr_5070_);
                    crate::leanh::lean_dec_ref_known(v_e_5027_, 2);
                    v_e_5027_ = v_expr_5070_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_5027_);
                    v___x_5072_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                    v___x_5073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5073_, 0, v___x_5072_);
                    return v___x_5073_;
                }
            },
            1 => {
                v___x_5036_ = (crate::leanh::lean_unbox(v_a_5032_) as u8);
                crate::leanh::lean_dec(v_a_5032_);
                if v___x_5036_ == 0 {
                    crate::leanh::lean_dec(v_declName_5030_);
                    v___x_5037_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                    if v_isShared_5035_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5034_, 0, v___x_5037_);
                        v___x_5039_ = v___x_5034_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5040_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5037_);
                        v___x_5039_ = v_reuseFailAlloc_5040_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5041_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5042_ = lean_mk_empty_array_with_capacity(v___x_5041_);
                    v___x_5043_ = lean_array_push(v___x_5042_, v_declName_5030_);
                    if v_isShared_5035_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5034_, 0, v___x_5043_);
                        v___x_5045_ = v___x_5034_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5046_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5043_);
                        v___x_5045_ = v_reuseFailAlloc_5046_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5039_;
            }
            3 => {
                return v___x_5045_;
            }
            4 => {
                if v_isShared_5051_ == 0 {
                    v___x_5053_ = v___x_5050_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
                    v___x_5053_ = v_reuseFailAlloc_5054_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5053_;
            }
            6 => {
                v___x_5065_ = l_Array_append___redArg(v_a_5061_, v_a_5059_);
                crate::leanh::lean_dec(v_a_5059_);
                if v_isShared_5064_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5063_, 0, v___x_5065_);
                    v___x_5067_ = v___x_5063_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 0, v___x_5065_);
                    v___x_5067_ = v_reuseFailAlloc_5068_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg___boxed(
    mut v_e_5074_: *mut crate::leanh::LeanObject,
    mut v_a_5075_: *mut crate::leanh::LeanObject,
    mut v_a_5076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5077_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_5074_, v_a_5075_);
    crate::leanh::lean_dec(v_a_5075_);
    return v_res_5077_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(
    mut v_e_5078_: *mut crate::leanh::LeanObject,
    mut v_a_5079_: *mut crate::leanh::LeanObject,
    mut v_a_5080_: *mut crate::leanh::LeanObject,
    mut v_a_5081_: *mut crate::leanh::LeanObject,
    mut v_a_5082_: *mut crate::leanh::LeanObject,
    mut v_a_5083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5085_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_5078_, v_a_5083_);
    return v___x_5085_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___boxed(
    mut v_e_5086_: *mut crate::leanh::LeanObject,
    mut v_a_5087_: *mut crate::leanh::LeanObject,
    mut v_a_5088_: *mut crate::leanh::LeanObject,
    mut v_a_5089_: *mut crate::leanh::LeanObject,
    mut v_a_5090_: *mut crate::leanh::LeanObject,
    mut v_a_5091_: *mut crate::leanh::LeanObject,
    mut v_a_5092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5093_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(v_e_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_, v_a_5091_);
    crate::leanh::lean_dec(v_a_5091_);
    crate::leanh::lean_dec_ref(v_a_5090_);
    crate::leanh::lean_dec(v_a_5089_);
    crate::leanh::lean_dec_ref(v_a_5088_);
    crate::leanh::lean_dec_ref(v_a_5087_);
    return v_res_5093_;
}
pub unsafe fn l_Lean_Server_locationLinksFromInstanceProjection(
    mut v_e_5094_: *mut crate::leanh::LeanObject,
    mut v_a_5095_: *mut crate::leanh::LeanObject,
    mut v_a_5096_: *mut crate::leanh::LeanObject,
    mut v_a_5097_: *mut crate::leanh::LeanObject,
    mut v_a_5098_: *mut crate::leanh::LeanObject,
    mut v_a_5099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5108_: u8 = 0;
    let mut v_val_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5113_: usize = 0;
    let mut v___x_5114_: usize = 0;
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut v_a_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5130_: u8 = 0;
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5134_: u8 = 0;
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5139_: u8 = 0;
    let mut v_a_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5143_: u8 = 0;
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5147_: u8 = 0;
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5101_ = l_Lean_Expr_getAppFn(v_e_5094_);
                v___x_5102_ = l_Lean_Expr_consumeMData(v___x_5101_);
                crate::leanh::lean_dec_ref(v___x_5101_);
                if crate::leanh::lean_obj_tag(v___x_5102_) == 4 {
                    v_declName_5103_ = crate::leanh::lean_ctor_get(v___x_5102_, 0);
                    crate::leanh::lean_inc(v_declName_5103_);
                    crate::leanh::lean_dec_ref_known(v___x_5102_, 2);
                    v___x_5104_ = l_Lean_Server_getInstanceProjectionArg_x3f(
                        v_e_5094_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5104_) == 0 {
                        v_a_5105_ = crate::leanh::lean_ctor_get(v___x_5104_, 0);
                        v_isSharedCheck_5139_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5104_)) as u8;
                        if v_isSharedCheck_5139_ == 0 {
                            v___x_5107_ = v___x_5104_;
                            v_isShared_5108_ = v_isSharedCheck_5139_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5105_);
                            crate::leanh::lean_dec(v___x_5104_);
                            v___x_5107_ = crate::leanh::lean_box(0);
                            v_isShared_5108_ = v_isSharedCheck_5139_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_5103_);
                        v_a_5140_ = crate::leanh::lean_ctor_get(v___x_5104_, 0);
                        v_isSharedCheck_5147_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5104_)) as u8;
                        if v_isSharedCheck_5147_ == 0 {
                            v___x_5142_ = v___x_5104_;
                            v_isShared_5143_ = v_isSharedCheck_5147_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5140_);
                            crate::leanh::lean_dec(v___x_5104_);
                            v___x_5142_ = crate::leanh::lean_box(0);
                            v_isShared_5143_ = v_isSharedCheck_5147_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5102_);
                    crate::leanh::lean_dec_ref(v_e_5094_);
                    v___x_5148_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v___x_5149_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5149_, 0, v___x_5148_);
                    return v___x_5149_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5105_) == 1 {
                    crate::leanh::lean_del_object(v___x_5107_);
                    v_val_5109_ = crate::leanh::lean_ctor_get(v_a_5105_, 0);
                    crate::leanh::lean_inc(v_val_5109_);
                    crate::leanh::lean_dec_ref_known(v_a_5105_, 1);
                    v___x_5110_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_val_5109_, v_a_5099_);
                    if crate::leanh::lean_obj_tag(v___x_5110_) == 0 {
                        v_a_5111_ = crate::leanh::lean_ctor_get(v___x_5110_, 0);
                        crate::leanh::lean_inc(v_a_5111_);
                        crate::leanh::lean_dec_ref_known(v___x_5110_, 1);
                        v___x_5112_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        v_sz_5113_ = lean_array_size(v_a_5111_);
                        v___x_5114_ = 0usize;
                        v___x_5115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_5111_, v_sz_5113_, v___x_5114_, v___x_5112_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_);
                        crate::leanh::lean_dec(v_a_5111_);
                        if crate::leanh::lean_obj_tag(v___x_5115_) == 0 {
                            v_a_5116_ = crate::leanh::lean_ctor_get(v___x_5115_, 0);
                            crate::leanh::lean_inc(v_a_5116_);
                            crate::leanh::lean_dec_ref_known(v___x_5115_, 1);
                            v___x_5117_ = l_Lean_Server_locationLinksFromDecl(
                                v_declName_5103_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                v_a_5099_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5117_) == 0 {
                                v_a_5118_ = crate::leanh::lean_ctor_get(v___x_5117_, 0);
                                v_isSharedCheck_5126_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5117_)) as u8;
                                if v_isSharedCheck_5126_ == 0 {
                                    v___x_5120_ = v___x_5117_;
                                    v_isShared_5121_ = v_isSharedCheck_5126_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5118_);
                                    crate::leanh::lean_dec(v___x_5117_);
                                    v___x_5120_ = crate::leanh::lean_box(0);
                                    v_isShared_5121_ = v_isSharedCheck_5126_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5116_);
                                return v___x_5117_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_declName_5103_);
                            return v___x_5115_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_5103_);
                        v_a_5127_ = crate::leanh::lean_ctor_get(v___x_5110_, 0);
                        v_isSharedCheck_5134_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5110_)) as u8;
                        if v_isSharedCheck_5134_ == 0 {
                            v___x_5129_ = v___x_5110_;
                            v_isShared_5130_ = v_isSharedCheck_5134_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5127_);
                            crate::leanh::lean_dec(v___x_5110_);
                            v___x_5129_ = crate::leanh::lean_box(0);
                            v_isShared_5130_ = v_isSharedCheck_5134_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5105_);
                    crate::leanh::lean_dec(v_declName_5103_);
                    v___x_5135_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_5108_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5107_, 0, v___x_5135_);
                        v___x_5137_ = v___x_5107_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5138_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5135_);
                        v___x_5137_ = v_reuseFailAlloc_5138_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5122_ = l_Array_append___redArg(v_a_5116_, v_a_5118_);
                crate::leanh::lean_dec(v_a_5118_);
                if v_isShared_5121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5120_, 0, v___x_5122_);
                    v___x_5124_ = v___x_5120_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 0, v___x_5122_);
                    v___x_5124_ = v_reuseFailAlloc_5125_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5124_;
            }
            4 => {
                if v_isShared_5130_ == 0 {
                    v___x_5132_ = v___x_5129_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
                    v___x_5132_ = v_reuseFailAlloc_5133_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5132_;
            }
            6 => {
                return v___x_5137_;
            }
            7 => {
                if v_isShared_5143_ == 0 {
                    v___x_5145_ = v___x_5142_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
                    v___x_5145_ = v_reuseFailAlloc_5146_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromInstanceProjection___boxed(
    mut v_e_5150_: *mut crate::leanh::LeanObject,
    mut v_a_5151_: *mut crate::leanh::LeanObject,
    mut v_a_5152_: *mut crate::leanh::LeanObject,
    mut v_a_5153_: *mut crate::leanh::LeanObject,
    mut v_a_5154_: *mut crate::leanh::LeanObject,
    mut v_a_5155_: *mut crate::leanh::LeanObject,
    mut v_a_5156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5157_ = l_Lean_Server_locationLinksFromInstanceProjection(
        v_e_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_,
    );
    crate::leanh::lean_dec(v_a_5155_);
    crate::leanh::lean_dec_ref(v_a_5154_);
    crate::leanh::lean_dec(v_a_5153_);
    crate::leanh::lean_dec_ref(v_a_5152_);
    crate::leanh::lean_dec_ref(v_a_5151_);
    return v_res_5157_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(
    mut v_as_5158_: *mut crate::leanh::LeanObject,
    mut v_sz_5159_: usize,
    mut v_i_5160_: usize,
    mut v_b_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_newLL_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: usize = 0;
    let mut v___x_5172_: usize = 0;
    let mut v___x_5174_: u8 = 0;
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5174_ = lean_usize_dec_lt(v_i_5160_, v_sz_5159_);
                if v___x_5174_ == 0 {
                    v___x_5175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5175_, 0, v_b_5161_);
                    return v___x_5175_;
                } else {
                    v_a_5176_ = lean_array_uget_borrowed(v_as_5158_, v_i_5160_);
                    v___x_5177_ = l_Lean_Expr_consumeMData(v_a_5176_);
                    match crate::leanh::lean_obj_tag(v___x_5177_) {
                        4 => {
                            v_declName_5178_ = crate::leanh::lean_ctor_get(v___x_5177_, 0);
                            crate::leanh::lean_inc(v_declName_5178_);
                            crate::leanh::lean_dec_ref_known(v___x_5177_, 2);
                            v___x_5179_ = l_Lean_Server_locationLinksFromDecl(
                                v_declName_5178_,
                                v___y_5162_,
                                v___y_5163_,
                                v___y_5164_,
                                v___y_5165_,
                                v___y_5166_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5179_) == 0 {
                                v_a_5180_ = crate::leanh::lean_ctor_get(v___x_5179_, 0);
                                crate::leanh::lean_inc(v_a_5180_);
                                crate::leanh::lean_dec_ref_known(v___x_5179_, 1);
                                v_newLL_5169_ = v_a_5180_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_5161_);
                                return v___x_5179_;
                            }
                        }
                        1 => {
                            v_fvarId_5181_ = crate::leanh::lean_ctor_get(v___x_5177_, 0);
                            crate::leanh::lean_inc(v_fvarId_5181_);
                            crate::leanh::lean_dec_ref_known(v___x_5177_, 1);
                            v___x_5182_ = l_Lean_Server_locationLinksFromBinder___redArg(
                                v_fvarId_5181_,
                                v___y_5162_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5182_) == 0 {
                                v_a_5183_ = crate::leanh::lean_ctor_get(v___x_5182_, 0);
                                crate::leanh::lean_inc(v_a_5183_);
                                crate::leanh::lean_dec_ref_known(v___x_5182_, 1);
                                v_newLL_5169_ = v_a_5183_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_5161_);
                                return v___x_5182_;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v___x_5177_);
                            crate::leanh::lean_inc(v_a_5176_);
                            v___x_5184_ = l_Lean_Server_locationLinksFromInstanceProjection(
                                v_a_5176_,
                                v___y_5162_,
                                v___y_5163_,
                                v___y_5164_,
                                v___y_5165_,
                                v___y_5166_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5184_) == 0 {
                                v_a_5185_ = crate::leanh::lean_ctor_get(v___x_5184_, 0);
                                crate::leanh::lean_inc(v_a_5185_);
                                crate::leanh::lean_dec_ref_known(v___x_5184_, 1);
                                v_newLL_5169_ = v_a_5185_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_5161_);
                                return v___x_5184_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5170_ = l_Array_append___redArg(v_b_5161_, v_newLL_5169_);
                crate::leanh::lean_dec_ref(v_newLL_5169_);
                v___x_5171_ = 1usize;
                v___x_5172_ = lean_usize_add(v_i_5160_, v___x_5171_);
                v_i_5160_ = v___x_5172_;
                v_b_5161_ = v___x_5170_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0___boxed(
    mut v_as_5186_: *mut crate::leanh::LeanObject,
    mut v_sz_5187_: *mut crate::leanh::LeanObject,
    mut v_i_5188_: *mut crate::leanh::LeanObject,
    mut v_b_5189_: *mut crate::leanh::LeanObject,
    mut v___y_5190_: *mut crate::leanh::LeanObject,
    mut v___y_5191_: *mut crate::leanh::LeanObject,
    mut v___y_5192_: *mut crate::leanh::LeanObject,
    mut v___y_5193_: *mut crate::leanh::LeanObject,
    mut v___y_5194_: *mut crate::leanh::LeanObject,
    mut v___y_5195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5196_: usize = 0;
    let mut v_i_boxed_5197_: usize = 0;
    let mut v_res_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5196_ = crate::leanh::lean_unbox_usize(v_sz_5187_);
    crate::leanh::lean_dec(v_sz_5187_);
    v_i_boxed_5197_ = crate::leanh::lean_unbox_usize(v_i_5188_);
    crate::leanh::lean_dec(v_i_5188_);
    v_res_5198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_as_5186_, v_sz_boxed_5196_, v_i_boxed_5197_, v_b_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
    crate::leanh::lean_dec(v___y_5194_);
    crate::leanh::lean_dec_ref(v___y_5193_);
    crate::leanh::lean_dec(v___y_5192_);
    crate::leanh::lean_dec_ref(v___y_5191_);
    crate::leanh::lean_dec_ref(v___y_5190_);
    crate::leanh::lean_dec_ref(v_as_5186_);
    return v_res_5198_;
}
pub unsafe fn l_Lean_Server_locationLinksFromTermInfo(
    mut v_ti_5199_: *mut crate::leanh::LeanObject,
    mut v_a_5200_: *mut crate::leanh::LeanObject,
    mut v_a_5201_: *mut crate::leanh::LeanObject,
    mut v_a_5202_: *mut crate::leanh::LeanObject,
    mut v_a_5203_: *mut crate::leanh::LeanObject,
    mut v_a_5204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_5206_: u8 = 0;
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5210_: usize = 0;
    let mut v___x_5211_: usize = 0;
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5216_: u8 = 0;
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_5206_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5200_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v___x_5207_ = l_Lean_Server_GoToKind_determineTargetExprs(
                    v_kind_5206_,
                    v_ti_5199_,
                    v_a_5201_,
                    v_a_5202_,
                    v_a_5203_,
                    v_a_5204_,
                );
                if crate::leanh::lean_obj_tag(v___x_5207_) == 0 {
                    v_a_5208_ = crate::leanh::lean_ctor_get(v___x_5207_, 0);
                    crate::leanh::lean_inc(v_a_5208_);
                    crate::leanh::lean_dec_ref_known(v___x_5207_, 1);
                    v___x_5209_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v_sz_5210_ = lean_array_size(v_a_5208_);
                    v___x_5211_ = 0usize;
                    v___x_5212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_a_5208_, v_sz_5210_, v___x_5211_, v___x_5209_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
                    crate::leanh::lean_dec(v_a_5208_);
                    return v___x_5212_;
                } else {
                    v_a_5213_ = crate::leanh::lean_ctor_get(v___x_5207_, 0);
                    v_isSharedCheck_5220_ = (!crate::leanh::lean_is_exclusive(v___x_5207_)) as u8;
                    if v_isSharedCheck_5220_ == 0 {
                        v___x_5215_ = v___x_5207_;
                        v_isShared_5216_ = v_isSharedCheck_5220_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5213_);
                        crate::leanh::lean_dec(v___x_5207_);
                        v___x_5215_ = crate::leanh::lean_box(0);
                        v_isShared_5216_ = v_isSharedCheck_5220_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5216_ == 0 {
                    v___x_5218_ = v___x_5215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
                    v___x_5218_ = v_reuseFailAlloc_5219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromTermInfo___boxed(
    mut v_ti_5221_: *mut crate::leanh::LeanObject,
    mut v_a_5222_: *mut crate::leanh::LeanObject,
    mut v_a_5223_: *mut crate::leanh::LeanObject,
    mut v_a_5224_: *mut crate::leanh::LeanObject,
    mut v_a_5225_: *mut crate::leanh::LeanObject,
    mut v_a_5226_: *mut crate::leanh::LeanObject,
    mut v_a_5227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_Lean_Server_locationLinksFromTermInfo(
        v_ti_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_,
    );
    crate::leanh::lean_dec(v_a_5226_);
    crate::leanh::lean_dec_ref(v_a_5225_);
    crate::leanh::lean_dec(v_a_5224_);
    crate::leanh::lean_dec_ref(v_a_5223_);
    crate::leanh::lean_dec_ref(v_a_5222_);
    return v_res_5228_;
}
pub unsafe fn l_Lean_Server_locationLinksFromDelabTermInfo(
    mut v_dti_5229_: *mut crate::leanh::LeanObject,
    mut v_a_5230_: *mut crate::leanh::LeanObject,
    mut v_a_5231_: *mut crate::leanh::LeanObject,
    mut v_a_5232_: *mut crate::leanh::LeanObject,
    mut v_a_5233_: *mut crate::leanh::LeanObject,
    mut v_a_5234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_location_x3f_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5240_: u8 = 0;
    let mut v_toTermInfo_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5246_: u8 = 0;
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v_val_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5255_: u8 = 0;
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5277_: u8 = 0;
    let mut v_text_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v_reuseFailAlloc_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5285_: u8 = 0;
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5287_: u8 = 0;
    let mut v_a_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5291_: u8 = 0;
    let mut v_ref_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5304_: u8 = 0;
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut v_isSharedCheck_5306_: u8 = 0;
    let mut v_toTermInfo_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_location_x3f_5236_ = crate::leanh::lean_ctor_get(v_dti_5229_, 1);
                crate::leanh::lean_inc(v_location_x3f_5236_);
                if crate::leanh::lean_obj_tag(v_location_x3f_5236_) == 1 {
                    v_val_5237_ = crate::leanh::lean_ctor_get(v_location_x3f_5236_, 0);
                    v_isSharedCheck_5306_ =
                        (!crate::leanh::lean_is_exclusive(v_location_x3f_5236_)) as u8;
                    if v_isSharedCheck_5306_ == 0 {
                        v___x_5239_ = v_location_x3f_5236_;
                        v_isShared_5240_ = v_isSharedCheck_5306_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5237_);
                        crate::leanh::lean_dec(v_location_x3f_5236_);
                        v___x_5239_ = crate::leanh::lean_box(0);
                        v_isShared_5240_ = v_isSharedCheck_5306_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_location_x3f_5236_);
                    v_toTermInfo_5307_ = crate::leanh::lean_ctor_get(v_dti_5229_, 0);
                    crate::leanh::lean_inc_ref(v_toTermInfo_5307_);
                    crate::leanh::lean_dec_ref(v_dti_5229_);
                    v___x_5308_ = l_Lean_Server_locationLinksFromTermInfo(
                        v_toTermInfo_5307_,
                        v_a_5230_,
                        v_a_5231_,
                        v_a_5232_,
                        v_a_5233_,
                        v_a_5234_,
                    );
                    return v___x_5308_;
                }
            }
            1 => {
                v_toTermInfo_5241_ = crate::leanh::lean_ctor_get(v_dti_5229_, 0);
                v_module_5242_ = crate::leanh::lean_ctor_get(v_val_5237_, 0);
                v_range_5243_ = crate::leanh::lean_ctor_get(v_val_5237_, 1);
                v_isSharedCheck_5305_ = (!crate::leanh::lean_is_exclusive(v_val_5237_)) as u8;
                if v_isSharedCheck_5305_ == 0 {
                    v___x_5245_ = v_val_5237_;
                    v_isShared_5246_ = v_isSharedCheck_5305_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_range_5243_);
                    crate::leanh::lean_inc(v_module_5242_);
                    crate::leanh::lean_dec(v_val_5237_);
                    v___x_5245_ = crate::leanh::lean_box(0);
                    v_isShared_5246_ = v_isSharedCheck_5305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5247_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5242_);
                if crate::leanh::lean_obj_tag(v___x_5247_) == 0 {
                    crate::leanh::lean_del_object(v___x_5245_);
                    crate::leanh::lean_del_object(v___x_5239_);
                    v_a_5248_ = crate::leanh::lean_ctor_get(v___x_5247_, 0);
                    v_isSharedCheck_5287_ = (!crate::leanh::lean_is_exclusive(v___x_5247_)) as u8;
                    if v_isSharedCheck_5287_ == 0 {
                        v___x_5250_ = v___x_5247_;
                        v_isShared_5251_ = v_isSharedCheck_5287_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5248_);
                        crate::leanh::lean_dec(v___x_5247_);
                        v___x_5250_ = crate::leanh::lean_box(0);
                        v_isShared_5251_ = v_isSharedCheck_5287_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_range_5243_);
                    crate::leanh::lean_dec_ref(v_dti_5229_);
                    v_a_5288_ = crate::leanh::lean_ctor_get(v___x_5247_, 0);
                    v_isSharedCheck_5304_ = (!crate::leanh::lean_is_exclusive(v___x_5247_)) as u8;
                    if v_isSharedCheck_5304_ == 0 {
                        v___x_5290_ = v___x_5247_;
                        v_isShared_5291_ = v_isSharedCheck_5304_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5288_);
                        crate::leanh::lean_dec(v___x_5247_);
                        v___x_5290_ = crate::leanh::lean_box(0);
                        v_isShared_5291_ = v_isSharedCheck_5304_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_5248_) == 1 {
                    v_val_5252_ = crate::leanh::lean_ctor_get(v_a_5248_, 0);
                    v_isSharedCheck_5285_ = (!crate::leanh::lean_is_exclusive(v_a_5248_)) as u8;
                    if v_isSharedCheck_5285_ == 0 {
                        v___x_5254_ = v_a_5248_;
                        v_isShared_5255_ = v_isSharedCheck_5285_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5252_);
                        crate::leanh::lean_dec(v_a_5248_);
                        v___x_5254_ = crate::leanh::lean_box(0);
                        v_isShared_5255_ = v_isSharedCheck_5285_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_toTermInfo_5241_);
                    crate::leanh::lean_del_object(v___x_5250_);
                    crate::leanh::lean_dec(v_a_5248_);
                    crate::leanh::lean_dec_ref(v_range_5243_);
                    crate::leanh::lean_dec_ref(v_dti_5229_);
                    v___x_5286_ = l_Lean_Server_locationLinksFromTermInfo(
                        v_toTermInfo_5241_,
                        v_a_5230_,
                        v_a_5231_,
                        v_a_5232_,
                        v_a_5233_,
                        v_a_5234_,
                    );
                    return v___x_5286_;
                }
            }
            4 => {
                v___x_5256_ = l_Lean_DeclarationRange_toLspRange(v_range_5243_);
                if v_isShared_5255_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5254_, 13);
                    crate::leanh::lean_ctor_set(v___x_5254_, 0, v_dti_5229_);
                    v___x_5270_ = v___x_5254_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5284_ = crate::leanh::lean_alloc_ctor(13, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 0, v_dti_5229_);
                    v___x_5270_ = v_reuseFailAlloc_5284_;
                    state = 7;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_5256_);
                v___x_5259_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5259_, 0, v___y_5258_);
                crate::leanh::lean_ctor_set(v___x_5259_, 1, v_val_5252_);
                crate::leanh::lean_ctor_set(v___x_5259_, 2, v___x_5256_);
                crate::leanh::lean_ctor_set(v___x_5259_, 3, v___x_5256_);
                v___x_5260_ = crate::leanh::lean_box(0);
                v___x_5261_ = 0;
                v___x_5262_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5262_, 0, v___x_5259_);
                crate::leanh::lean_ctor_set(v___x_5262_, 1, v___x_5260_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5262_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5261_,
                );
                v___x_5263_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5264_ = lean_mk_empty_array_with_capacity(v___x_5263_);
                v___x_5265_ = lean_array_push(v___x_5264_, v___x_5262_);
                if v_isShared_5251_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5250_, 0, v___x_5265_);
                    v___x_5267_ = v___x_5250_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5268_, 0, v___x_5265_);
                    v___x_5267_ = v_reuseFailAlloc_5268_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5267_;
            }
            7 => {
                v___x_5271_ = l_Lean_Elab_Info_range_x3f(v___x_5270_);
                crate::leanh::lean_dec_ref(v___x_5270_);
                if crate::leanh::lean_obj_tag(v___x_5271_) == 0 {
                    v___x_5272_ = crate::leanh::lean_box(0);
                    v___y_5258_ = v___x_5272_;
                    state = 5;
                    continue;
                } else {
                    v_doc_5273_ = crate::leanh::lean_ctor_get(v_a_5230_, 0);
                    v_val_5274_ = crate::leanh::lean_ctor_get(v___x_5271_, 0);
                    v_isSharedCheck_5283_ = (!crate::leanh::lean_is_exclusive(v___x_5271_)) as u8;
                    if v_isSharedCheck_5283_ == 0 {
                        v___x_5276_ = v___x_5271_;
                        v_isShared_5277_ = v_isSharedCheck_5283_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5274_);
                        crate::leanh::lean_dec(v___x_5271_);
                        v___x_5276_ = crate::leanh::lean_box(0);
                        v_isShared_5277_ = v_isSharedCheck_5283_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v_text_5278_ = crate::leanh::lean_ctor_get(v_doc_5273_, 3);
                crate::leanh::lean_inc_ref(v_text_5278_);
                v___x_5279_ = l_Lean_Syntax_Range_toLspRange(v_text_5278_, v_val_5274_);
                if v_isShared_5277_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5276_, 0, v___x_5279_);
                    v___x_5281_ = v___x_5276_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5279_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_5258_ = v___x_5281_;
                state = 5;
                continue;
            }
            10 => {
                v_ref_5292_ = crate::leanh::lean_ctor_get(v_a_5233_, 5);
                v___x_5293_ = lean_io_error_to_string(v_a_5288_);
                if v_isShared_5240_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5239_, 3);
                    crate::leanh::lean_ctor_set(v___x_5239_, 0, v___x_5293_);
                    v___x_5295_ = v___x_5239_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5303_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5293_);
                    v___x_5295_ = v_reuseFailAlloc_5303_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_5296_ = l_Lean_MessageData_ofFormat(v___x_5295_);
                crate::leanh::lean_inc(v_ref_5292_);
                if v_isShared_5246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5245_, 1, v___x_5296_);
                    crate::leanh::lean_ctor_set(v___x_5245_, 0, v_ref_5292_);
                    v___x_5298_ = v___x_5245_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5302_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_ref_5292_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5302_, 1, v___x_5296_);
                    v___x_5298_ = v_reuseFailAlloc_5302_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_5291_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5290_, 0, v___x_5298_);
                    v___x_5300_ = v___x_5290_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5298_);
                    v___x_5300_ = v_reuseFailAlloc_5301_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromDelabTermInfo___boxed(
    mut v_dti_5309_: *mut crate::leanh::LeanObject,
    mut v_a_5310_: *mut crate::leanh::LeanObject,
    mut v_a_5311_: *mut crate::leanh::LeanObject,
    mut v_a_5312_: *mut crate::leanh::LeanObject,
    mut v_a_5313_: *mut crate::leanh::LeanObject,
    mut v_a_5314_: *mut crate::leanh::LeanObject,
    mut v_a_5315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5316_ = l_Lean_Server_locationLinksFromDelabTermInfo(
        v_dti_5309_,
        v_a_5310_,
        v_a_5311_,
        v_a_5312_,
        v_a_5313_,
        v_a_5314_,
    );
    crate::leanh::lean_dec(v_a_5314_);
    crate::leanh::lean_dec_ref(v_a_5313_);
    crate::leanh::lean_dec(v_a_5312_);
    crate::leanh::lean_dec_ref(v_a_5311_);
    crate::leanh::lean_dec_ref(v_a_5310_);
    return v_res_5316_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(
    mut v_e_5317_: *mut crate::leanh::LeanObject,
    mut v___y_5318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5320_: u8 = 0;
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5334_: u8 = 0;
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5340_: u8 = 0;
    let mut v_unused_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5320_ = l_Lean_Expr_hasMVar(v_e_5317_);
                if v___x_5320_ == 0 {
                    v___x_5321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5321_, 0, v_e_5317_);
                    return v___x_5321_;
                } else {
                    v___x_5322_ = lean_st_ref_get(v___y_5318_);
                    v_mctx_5323_ = crate::leanh::lean_ctor_get(v___x_5322_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5323_);
                    crate::leanh::lean_dec(v___x_5322_);
                    v___x_5324_ = l_Lean_instantiateMVarsCore(v_mctx_5323_, v_e_5317_);
                    v_fst_5325_ = crate::leanh::lean_ctor_get(v___x_5324_, 0);
                    crate::leanh::lean_inc(v_fst_5325_);
                    v_snd_5326_ = crate::leanh::lean_ctor_get(v___x_5324_, 1);
                    crate::leanh::lean_inc(v_snd_5326_);
                    crate::leanh::lean_dec_ref(v___x_5324_);
                    v___x_5327_ = lean_st_ref_take(v___y_5318_);
                    v_cache_5328_ = crate::leanh::lean_ctor_get(v___x_5327_, 1);
                    v_zetaDeltaFVarIds_5329_ = crate::leanh::lean_ctor_get(v___x_5327_, 2);
                    v_postponed_5330_ = crate::leanh::lean_ctor_get(v___x_5327_, 3);
                    v_diag_5331_ = crate::leanh::lean_ctor_get(v___x_5327_, 4);
                    v_isSharedCheck_5340_ = (!crate::leanh::lean_is_exclusive(v___x_5327_)) as u8;
                    if v_isSharedCheck_5340_ == 0 {
                        v_unused_5341_ = crate::leanh::lean_ctor_get(v___x_5327_, 0);
                        crate::leanh::lean_dec(v_unused_5341_);
                        v___x_5333_ = v___x_5327_;
                        v_isShared_5334_ = v_isSharedCheck_5340_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5331_);
                        crate::leanh::lean_inc(v_postponed_5330_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5329_);
                        crate::leanh::lean_inc(v_cache_5328_);
                        crate::leanh::lean_dec(v___x_5327_);
                        v___x_5333_ = crate::leanh::lean_box(0);
                        v_isShared_5334_ = v_isSharedCheck_5340_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5333_, 0, v_snd_5326_);
                    v___x_5336_ = v___x_5333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5339_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_snd_5326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 1, v_cache_5328_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5339_,
                        2,
                        v_zetaDeltaFVarIds_5329_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 3, v_postponed_5330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 4, v_diag_5331_);
                    v___x_5336_ = v_reuseFailAlloc_5339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5337_ = lean_st_ref_set(v___y_5318_, v___x_5336_);
                v___x_5338_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5338_, 0, v_fst_5325_);
                return v___x_5338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg___boxed(
    mut v_e_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5345_ =
        l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(
            v_e_5342_,
            v___y_5343_,
        );
    crate::leanh::lean_dec(v___y_5343_);
    return v_res_5345_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(
    mut v_e_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
    mut v___y_5349_: *mut crate::leanh::LeanObject,
    mut v___y_5350_: *mut crate::leanh::LeanObject,
    mut v___y_5351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5353_ =
        l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(
            v_e_5346_,
            v___y_5349_,
        );
    return v___x_5353_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___boxed(
    mut v_e_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
    mut v___y_5356_: *mut crate::leanh::LeanObject,
    mut v___y_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5361_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(
        v_e_5354_,
        v___y_5355_,
        v___y_5356_,
        v___y_5357_,
        v___y_5358_,
        v___y_5359_,
    );
    crate::leanh::lean_dec(v___y_5359_);
    crate::leanh::lean_dec_ref(v___y_5358_);
    crate::leanh::lean_dec(v___y_5357_);
    crate::leanh::lean_dec_ref(v___y_5356_);
    crate::leanh::lean_dec_ref(v___y_5355_);
    return v_res_5361_;
}
pub unsafe fn l_Lean_Server_locationLinksFromFieldInfo(
    mut v_fi_5362_: *mut crate::leanh::LeanObject,
    mut v_a_5363_: *mut crate::leanh::LeanObject,
    mut v_a_5364_: *mut crate::leanh::LeanObject,
    mut v_a_5365_: *mut crate::leanh::LeanObject,
    mut v_a_5366_: *mut crate::leanh::LeanObject,
    mut v_a_5367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_5369_: u8 = 0;
    let mut v___x_5370_: u8 = 0;
    let mut v___x_5371_: u8 = 0;
    let mut v_projName_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5381_: u8 = 0;
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5390_: u8 = 0;
    let mut v_a_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_5369_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5363_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v___x_5370_ = 2;
                v___x_5371_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_5369_, v___x_5370_);
                if v___x_5371_ == 0 {
                    v_projName_5372_ = crate::leanh::lean_ctor_get(v_fi_5362_, 0);
                    crate::leanh::lean_inc(v_projName_5372_);
                    crate::leanh::lean_dec_ref(v_fi_5362_);
                    v___x_5373_ = l_Lean_Server_locationLinksFromDecl(
                        v_projName_5372_,
                        v_a_5363_,
                        v_a_5364_,
                        v_a_5365_,
                        v_a_5366_,
                        v_a_5367_,
                    );
                    return v___x_5373_;
                } else {
                    v_val_5374_ = crate::leanh::lean_ctor_get(v_fi_5362_, 3);
                    crate::leanh::lean_inc_ref(v_val_5374_);
                    crate::leanh::lean_dec_ref(v_fi_5362_);
                    crate::leanh::lean_inc(v_a_5367_);
                    crate::leanh::lean_inc_ref(v_a_5366_);
                    crate::leanh::lean_inc(v_a_5365_);
                    crate::leanh::lean_inc_ref(v_a_5364_);
                    v___x_5375_ =
                        lean_infer_type(v_val_5374_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_);
                    if crate::leanh::lean_obj_tag(v___x_5375_) == 0 {
                        v_a_5376_ = crate::leanh::lean_ctor_get(v___x_5375_, 0);
                        crate::leanh::lean_inc(v_a_5376_);
                        crate::leanh::lean_dec_ref_known(v___x_5375_, 1);
                        v___x_5377_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_a_5376_, v_a_5365_);
                        v_a_5378_ = crate::leanh::lean_ctor_get(v___x_5377_, 0);
                        v_isSharedCheck_5390_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5377_)) as u8;
                        if v_isSharedCheck_5390_ == 0 {
                            v___x_5380_ = v___x_5377_;
                            v_isShared_5381_ = v_isSharedCheck_5390_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5378_);
                            crate::leanh::lean_dec(v___x_5377_);
                            v___x_5380_ = crate::leanh::lean_box(0);
                            v_isShared_5381_ = v_isSharedCheck_5390_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5391_ = crate::leanh::lean_ctor_get(v___x_5375_, 0);
                        v_isSharedCheck_5398_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5375_)) as u8;
                        if v_isSharedCheck_5398_ == 0 {
                            v___x_5393_ = v___x_5375_;
                            v_isShared_5394_ = v_isSharedCheck_5398_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5391_);
                            crate::leanh::lean_dec(v___x_5375_);
                            v___x_5393_ = crate::leanh::lean_box(0);
                            v_isShared_5394_ = v_isSharedCheck_5398_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5382_ = l_Lean_Expr_getAppFn(v_a_5378_);
                crate::leanh::lean_dec(v_a_5378_);
                v___x_5383_ = l_Lean_Expr_constName_x3f(v___x_5382_);
                crate::leanh::lean_dec_ref(v___x_5382_);
                if crate::leanh::lean_obj_tag(v___x_5383_) == 1 {
                    crate::leanh::lean_del_object(v___x_5380_);
                    v_val_5384_ = crate::leanh::lean_ctor_get(v___x_5383_, 0);
                    crate::leanh::lean_inc(v_val_5384_);
                    crate::leanh::lean_dec_ref_known(v___x_5383_, 1);
                    v___x_5385_ = l_Lean_Server_locationLinksFromDecl(
                        v_val_5384_,
                        v_a_5363_,
                        v_a_5364_,
                        v_a_5365_,
                        v_a_5366_,
                        v_a_5367_,
                    );
                    return v___x_5385_;
                } else {
                    crate::leanh::lean_dec(v___x_5383_);
                    v___x_5386_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_5381_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5380_, 0, v___x_5386_);
                        v___x_5388_ = v___x_5380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5389_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5389_, 0, v___x_5386_);
                        v___x_5388_ = v_reuseFailAlloc_5389_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5388_;
            }
            3 => {
                if v_isShared_5394_ == 0 {
                    v___x_5396_ = v___x_5393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_a_5391_);
                    v___x_5396_ = v_reuseFailAlloc_5397_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromFieldInfo___boxed(
    mut v_fi_5399_: *mut crate::leanh::LeanObject,
    mut v_a_5400_: *mut crate::leanh::LeanObject,
    mut v_a_5401_: *mut crate::leanh::LeanObject,
    mut v_a_5402_: *mut crate::leanh::LeanObject,
    mut v_a_5403_: *mut crate::leanh::LeanObject,
    mut v_a_5404_: *mut crate::leanh::LeanObject,
    mut v_a_5405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5406_ = l_Lean_Server_locationLinksFromFieldInfo(
        v_fi_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_,
    );
    crate::leanh::lean_dec(v_a_5404_);
    crate::leanh::lean_dec_ref(v_a_5403_);
    crate::leanh::lean_dec(v_a_5402_);
    crate::leanh::lean_dec_ref(v_a_5401_);
    crate::leanh::lean_dec_ref(v_a_5400_);
    return v_res_5406_;
}
pub unsafe fn l_Lean_Server_locationLinksFromOptionInfo(
    mut v_i_5407_: *mut crate::leanh::LeanObject,
    mut v_a_5408_: *mut crate::leanh::LeanObject,
    mut v_a_5409_: *mut crate::leanh::LeanObject,
    mut v_a_5410_: *mut crate::leanh::LeanObject,
    mut v_a_5411_: *mut crate::leanh::LeanObject,
    mut v_a_5412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_declName_5414_ = crate::leanh::lean_ctor_get(v_i_5407_, 2);
    crate::leanh::lean_inc(v_declName_5414_);
    crate::leanh::lean_dec_ref(v_i_5407_);
    v___x_5415_ = l_Lean_Server_locationLinksFromDecl(
        v_declName_5414_,
        v_a_5408_,
        v_a_5409_,
        v_a_5410_,
        v_a_5411_,
        v_a_5412_,
    );
    return v___x_5415_;
}
pub unsafe fn l_Lean_Server_locationLinksFromOptionInfo___boxed(
    mut v_i_5416_: *mut crate::leanh::LeanObject,
    mut v_a_5417_: *mut crate::leanh::LeanObject,
    mut v_a_5418_: *mut crate::leanh::LeanObject,
    mut v_a_5419_: *mut crate::leanh::LeanObject,
    mut v_a_5420_: *mut crate::leanh::LeanObject,
    mut v_a_5421_: *mut crate::leanh::LeanObject,
    mut v_a_5422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5423_ = l_Lean_Server_locationLinksFromOptionInfo(
        v_i_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_,
    );
    crate::leanh::lean_dec(v_a_5421_);
    crate::leanh::lean_dec_ref(v_a_5420_);
    crate::leanh::lean_dec(v_a_5419_);
    crate::leanh::lean_dec_ref(v_a_5418_);
    crate::leanh::lean_dec_ref(v_a_5417_);
    return v_res_5423_;
}
pub unsafe fn l_Lean_Server_locationLinksFromCommandInfo___redArg(
    mut v_i_5424_: *mut crate::leanh::LeanObject,
    mut v_a_5425_: *mut crate::leanh::LeanObject,
    mut v_a_5426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elaborator_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: u8 = 0;
    let mut v_kind_5436_: u8 = 0;
    let mut v___x_5437_: u8 = 0;
    let mut v___x_5438_: u8 = 0;
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elaborator_5431_ = crate::leanh::lean_ctor_get(v_i_5424_, 0);
                if crate::leanh::lean_obj_tag(v_elaborator_5431_) == 1 {
                    v_pre_5432_ = crate::leanh::lean_ctor_get(v_elaborator_5431_, 0);
                    if crate::leanh::lean_obj_tag(v_pre_5432_) == 0 {
                        v_str_5433_ = crate::leanh::lean_ctor_get(v_elaborator_5431_, 1);
                        v___x_5434_ = l_Lean_Server_locationLinksFromImport___redArg___closed__3;
                        v___x_5435_ = lean_string_dec_eq(v_str_5433_, v___x_5434_);
                        if v___x_5435_ == 0 {
                            crate::leanh::lean_dec_ref(v_i_5424_);
                            state = 1;
                            continue;
                        } else {
                            v_kind_5436_ = crate::leanh::lean_ctor_get_uint8(
                                v_a_5425_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            );
                            v___x_5437_ = 2;
                            v___x_5438_ =
                                l_Lean_Server_instBEqGoToKind_beq(v_kind_5436_, v___x_5437_);
                            if v___x_5438_ == 0 {
                                v___x_5439_ = l_Lean_Server_locationLinksFromImport___redArg(
                                    v_i_5424_, v_a_5425_, v_a_5426_,
                                );
                                return v___x_5439_;
                            } else {
                                crate::leanh::lean_dec_ref(v_i_5424_);
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_i_5424_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_i_5424_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5429_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                v___x_5430_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5430_, 0, v___x_5429_);
                return v___x_5430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromCommandInfo___redArg___boxed(
    mut v_i_5440_: *mut crate::leanh::LeanObject,
    mut v_a_5441_: *mut crate::leanh::LeanObject,
    mut v_a_5442_: *mut crate::leanh::LeanObject,
    mut v_a_5443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5444_ =
        l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_5440_, v_a_5441_, v_a_5442_);
    crate::leanh::lean_dec_ref(v_a_5442_);
    crate::leanh::lean_dec_ref(v_a_5441_);
    return v_res_5444_;
}
pub unsafe fn l_Lean_Server_locationLinksFromCommandInfo(
    mut v_i_5445_: *mut crate::leanh::LeanObject,
    mut v_a_5446_: *mut crate::leanh::LeanObject,
    mut v_a_5447_: *mut crate::leanh::LeanObject,
    mut v_a_5448_: *mut crate::leanh::LeanObject,
    mut v_a_5449_: *mut crate::leanh::LeanObject,
    mut v_a_5450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5452_ =
        l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_5445_, v_a_5446_, v_a_5449_);
    return v___x_5452_;
}
pub unsafe fn l_Lean_Server_locationLinksFromCommandInfo___boxed(
    mut v_i_5453_: *mut crate::leanh::LeanObject,
    mut v_a_5454_: *mut crate::leanh::LeanObject,
    mut v_a_5455_: *mut crate::leanh::LeanObject,
    mut v_a_5456_: *mut crate::leanh::LeanObject,
    mut v_a_5457_: *mut crate::leanh::LeanObject,
    mut v_a_5458_: *mut crate::leanh::LeanObject,
    mut v_a_5459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5460_ = l_Lean_Server_locationLinksFromCommandInfo(
        v_i_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_,
    );
    crate::leanh::lean_dec(v_a_5458_);
    crate::leanh::lean_dec_ref(v_a_5457_);
    crate::leanh::lean_dec(v_a_5456_);
    crate::leanh::lean_dec_ref(v_a_5455_);
    crate::leanh::lean_dec_ref(v_a_5454_);
    return v_res_5460_;
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo___lam__0(
    mut v_kind_5461_: u8,
    mut v_ll_5462_: *mut crate::leanh::LeanObject,
    mut v___y_5463_: *mut crate::leanh::LeanObject,
    mut v___y_5464_: *mut crate::leanh::LeanObject,
    mut v___y_5465_: *mut crate::leanh::LeanObject,
    mut v___y_5466_: *mut crate::leanh::LeanObject,
    mut v___y_5467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5470_: u8 = 0;
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5476_: u8 = 0;
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5481_: u8 = 0;
    let mut v___x_5482_: u8 = 0;
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5482_ = 0;
                v___x_5483_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_5461_, v___x_5482_);
                if v___x_5483_ == 0 {
                    v___x_5484_ = lean_array_get_size(v_ll_5462_);
                    v___x_5485_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5486_ = lean_nat_dec_eq(v___x_5484_, v___x_5485_);
                    v___y_5470_ = v___x_5486_;
                    state = 1;
                    continue;
                } else {
                    v___y_5470_ = v___x_5483_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_5470_ == 0 {
                    v___x_5471_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5471_, 0, v_ll_5462_);
                    return v___x_5471_;
                } else {
                    v___x_5472_ = l_Lean_Server_locationLinksDefault(
                        v___y_5463_,
                        v___y_5464_,
                        v___y_5465_,
                        v___y_5466_,
                        v___y_5467_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5472_) == 0 {
                        v_a_5473_ = crate::leanh::lean_ctor_get(v___x_5472_, 0);
                        v_isSharedCheck_5481_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5472_)) as u8;
                        if v_isSharedCheck_5481_ == 0 {
                            v___x_5475_ = v___x_5472_;
                            v_isShared_5476_ = v_isSharedCheck_5481_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5473_);
                            crate::leanh::lean_dec(v___x_5472_);
                            v___x_5475_ = crate::leanh::lean_box(0);
                            v_isShared_5476_ = v_isSharedCheck_5481_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ll_5462_);
                        return v___x_5472_;
                    }
                }
            }
            2 => {
                v___x_5477_ = l_Array_append___redArg(v_ll_5462_, v_a_5473_);
                crate::leanh::lean_dec(v_a_5473_);
                if v_isShared_5476_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5475_, 0, v___x_5477_);
                    v___x_5479_ = v___x_5475_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5477_);
                    v___x_5479_ = v_reuseFailAlloc_5480_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo___lam__0___boxed(
    mut v_kind_5487_: *mut crate::leanh::LeanObject,
    mut v_ll_5488_: *mut crate::leanh::LeanObject,
    mut v___y_5489_: *mut crate::leanh::LeanObject,
    mut v___y_5490_: *mut crate::leanh::LeanObject,
    mut v___y_5491_: *mut crate::leanh::LeanObject,
    mut v___y_5492_: *mut crate::leanh::LeanObject,
    mut v___y_5493_: *mut crate::leanh::LeanObject,
    mut v___y_5494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_5495_: u8 = 0;
    let mut v_res_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5495_ = (crate::leanh::lean_unbox(v_kind_5487_) as u8);
    v_res_5496_ = l_Lean_Server_locationLinksOfInfo___lam__0(
        v_kind_boxed_5495_,
        v_ll_5488_,
        v___y_5489_,
        v___y_5490_,
        v___y_5491_,
        v___y_5492_,
        v___y_5493_,
    );
    crate::leanh::lean_dec(v___y_5493_);
    crate::leanh::lean_dec_ref(v___y_5492_);
    crate::leanh::lean_dec(v___y_5491_);
    crate::leanh::lean_dec_ref(v___y_5490_);
    crate::leanh::lean_dec_ref(v___y_5489_);
    return v_res_5496_;
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo___lam__1(
    mut v_info_5497_: *mut crate::leanh::LeanObject,
    mut v___f_5498_: *mut crate::leanh::LeanObject,
    mut v___y_5499_: *mut crate::leanh::LeanObject,
    mut v___y_5500_: *mut crate::leanh::LeanObject,
    mut v___y_5501_: *mut crate::leanh::LeanObject,
    mut v___y_5502_: *mut crate::leanh::LeanObject,
    mut v___y_5503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_info_5497_) {
        1 => {
            let mut v_i_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_5505_ = crate::leanh::lean_ctor_get(v_info_5497_, 0);
            crate::leanh::lean_inc_ref(v_i_5505_);
            crate::leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5506_ = l_Lean_Server_locationLinksFromTermInfo(
                v_i_5505_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if crate::leanh::lean_obj_tag(v___x_5506_) == 0 {
                let mut v_a_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5507_ = crate::leanh::lean_ctor_get(v___x_5506_, 0);
                crate::leanh::lean_inc(v_a_5507_);
                crate::leanh::lean_dec_ref_known(v___x_5506_, 1);
                crate::leanh::lean_inc(v___y_5503_);
                crate::leanh::lean_inc_ref(v___y_5502_);
                crate::leanh::lean_inc(v___y_5501_);
                crate::leanh::lean_inc_ref(v___y_5500_);
                crate::leanh::lean_inc_ref(v___y_5499_);
                v___x_5508_ = crate::leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5507_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5508_;
            } else {
                crate::leanh::lean_dec_ref(v___f_5498_);
                return v___x_5506_;
            }
        }
        13 => {
            let mut v_i_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_5509_ = crate::leanh::lean_ctor_get(v_info_5497_, 0);
            crate::leanh::lean_inc_ref(v_i_5509_);
            crate::leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5510_ = l_Lean_Server_locationLinksFromDelabTermInfo(
                v_i_5509_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if crate::leanh::lean_obj_tag(v___x_5510_) == 0 {
                let mut v_a_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5511_ = crate::leanh::lean_ctor_get(v___x_5510_, 0);
                crate::leanh::lean_inc(v_a_5511_);
                crate::leanh::lean_dec_ref_known(v___x_5510_, 1);
                crate::leanh::lean_inc(v___y_5503_);
                crate::leanh::lean_inc_ref(v___y_5502_);
                crate::leanh::lean_inc(v___y_5501_);
                crate::leanh::lean_inc_ref(v___y_5500_);
                crate::leanh::lean_inc_ref(v___y_5499_);
                v___x_5512_ = crate::leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5511_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5512_;
            } else {
                crate::leanh::lean_dec_ref(v___f_5498_);
                return v___x_5510_;
            }
        }
        7 => {
            let mut v_i_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_5513_ = crate::leanh::lean_ctor_get(v_info_5497_, 0);
            crate::leanh::lean_inc_ref(v_i_5513_);
            crate::leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5514_ = l_Lean_Server_locationLinksFromFieldInfo(
                v_i_5513_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if crate::leanh::lean_obj_tag(v___x_5514_) == 0 {
                let mut v_a_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5515_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                crate::leanh::lean_inc(v_a_5515_);
                crate::leanh::lean_dec_ref_known(v___x_5514_, 1);
                crate::leanh::lean_inc(v___y_5503_);
                crate::leanh::lean_inc_ref(v___y_5502_);
                crate::leanh::lean_inc(v___y_5501_);
                crate::leanh::lean_inc_ref(v___y_5500_);
                crate::leanh::lean_inc_ref(v___y_5499_);
                v___x_5516_ = crate::leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5515_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5516_;
            } else {
                crate::leanh::lean_dec_ref(v___f_5498_);
                return v___x_5514_;
            }
        }
        5 => {
            let mut v_i_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_5517_ = crate::leanh::lean_ctor_get(v_info_5497_, 0);
            crate::leanh::lean_inc_ref(v_i_5517_);
            crate::leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5518_ = l_Lean_Server_locationLinksFromOptionInfo(
                v_i_5517_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if crate::leanh::lean_obj_tag(v___x_5518_) == 0 {
                let mut v_a_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5519_ = crate::leanh::lean_ctor_get(v___x_5518_, 0);
                crate::leanh::lean_inc(v_a_5519_);
                crate::leanh::lean_dec_ref_known(v___x_5518_, 1);
                crate::leanh::lean_inc(v___y_5503_);
                crate::leanh::lean_inc_ref(v___y_5502_);
                crate::leanh::lean_inc(v___y_5501_);
                crate::leanh::lean_inc_ref(v___y_5500_);
                crate::leanh::lean_inc_ref(v___y_5499_);
                v___x_5520_ = crate::leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5519_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5520_;
            } else {
                crate::leanh::lean_dec_ref(v___f_5498_);
                return v___x_5518_;
            }
        }
        3 => {
            let mut v_i_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_5521_ = crate::leanh::lean_ctor_get(v_info_5497_, 0);
            crate::leanh::lean_inc_ref(v_i_5521_);
            crate::leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5522_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(
                v_i_5521_,
                v___y_5499_,
                v___y_5502_,
            );
            if crate::leanh::lean_obj_tag(v___x_5522_) == 0 {
                let mut v_a_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5523_ = crate::leanh::lean_ctor_get(v___x_5522_, 0);
                crate::leanh::lean_inc(v_a_5523_);
                crate::leanh::lean_dec_ref_known(v___x_5522_, 1);
                crate::leanh::lean_inc(v___y_5503_);
                crate::leanh::lean_inc_ref(v___y_5502_);
                crate::leanh::lean_inc(v___y_5501_);
                crate::leanh::lean_inc_ref(v___y_5500_);
                crate::leanh::lean_inc_ref(v___y_5499_);
                v___x_5524_ = crate::leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5523_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5524_;
            } else {
                crate::leanh::lean_dec_ref(v___f_5498_);
                return v___x_5522_;
            }
        }
        6 => {
            let mut v_i_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_5525_ = crate::leanh::lean_ctor_get(v_info_5497_, 0);
            crate::leanh::lean_inc_ref(v_i_5525_);
            crate::leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5526_ = l_Lean_Server_locationLinksFromErrorNameInfo(
                v_i_5525_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            crate::leanh::lean_dec_ref(v_i_5525_);
            if crate::leanh::lean_obj_tag(v___x_5526_) == 0 {
                let mut v_a_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5527_ = crate::leanh::lean_ctor_get(v___x_5526_, 0);
                crate::leanh::lean_inc(v_a_5527_);
                crate::leanh::lean_dec_ref_known(v___x_5526_, 1);
                crate::leanh::lean_inc(v___y_5503_);
                crate::leanh::lean_inc_ref(v___y_5502_);
                crate::leanh::lean_inc(v___y_5501_);
                crate::leanh::lean_inc_ref(v___y_5500_);
                crate::leanh::lean_inc_ref(v___y_5499_);
                v___x_5528_ = crate::leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5527_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5528_;
            } else {
                crate::leanh::lean_dec_ref(v___f_5498_);
                return v___x_5526_;
            }
        }
        16 => {
            let mut v_i_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_5529_ = crate::leanh::lean_ctor_get(v_info_5497_, 0);
            crate::leanh::lean_inc_ref(v_i_5529_);
            crate::leanh::lean_dec_ref_known(v_info_5497_, 1);
            v_name_5530_ = crate::leanh::lean_ctor_get(v_i_5529_, 1);
            crate::leanh::lean_inc(v_name_5530_);
            crate::leanh::lean_dec_ref(v_i_5529_);
            v___x_5531_ = l_Lean_Server_locationLinksFromDecl(
                v_name_5530_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if crate::leanh::lean_obj_tag(v___x_5531_) == 0 {
                let mut v_a_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_5532_ = crate::leanh::lean_ctor_get(v___x_5531_, 0);
                crate::leanh::lean_inc(v_a_5532_);
                crate::leanh::lean_dec_ref_known(v___x_5531_, 1);
                crate::leanh::lean_inc(v___y_5503_);
                crate::leanh::lean_inc_ref(v___y_5502_);
                crate::leanh::lean_inc(v___y_5501_);
                crate::leanh::lean_inc_ref(v___y_5500_);
                crate::leanh::lean_inc_ref(v___y_5499_);
                v___x_5533_ = crate::leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5532_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5533_;
            } else {
                crate::leanh::lean_dec_ref(v___f_5498_);
                return v___x_5531_;
            }
        }
        _ => {
            let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_info_5497_);
            v___x_5534_ = l_Lean_Server_locationLinksFromDecl___closed__0;
            crate::leanh::lean_inc(v___y_5503_);
            crate::leanh::lean_inc_ref(v___y_5502_);
            crate::leanh::lean_inc(v___y_5501_);
            crate::leanh::lean_inc_ref(v___y_5500_);
            crate::leanh::lean_inc_ref(v___y_5499_);
            v___x_5535_ = crate::leanh::lean_apply_7(
                v___f_5498_,
                v___x_5534_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
                crate::leanh::lean_box(0),
            );
            return v___x_5535_;
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo___lam__1___boxed(
    mut v_info_5536_: *mut crate::leanh::LeanObject,
    mut v___f_5537_: *mut crate::leanh::LeanObject,
    mut v___y_5538_: *mut crate::leanh::LeanObject,
    mut v___y_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
    mut v___y_5543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5544_ = l_Lean_Server_locationLinksOfInfo___lam__1(
        v_info_5536_,
        v___f_5537_,
        v___y_5538_,
        v___y_5539_,
        v___y_5540_,
        v___y_5541_,
        v___y_5542_,
    );
    crate::leanh::lean_dec(v___y_5542_);
    crate::leanh::lean_dec_ref(v___y_5541_);
    crate::leanh::lean_dec(v___y_5540_);
    crate::leanh::lean_dec_ref(v___y_5539_);
    crate::leanh::lean_dec_ref(v___y_5538_);
    return v_res_5544_;
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo(
    mut v_doc_5545_: *mut crate::leanh::LeanObject,
    mut v_kind_5546_: u8,
    mut v_ictx_5547_: *mut crate::leanh::LeanObject,
    mut v_infoTree_x3f_5548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctx_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ctx_5550_ = crate::leanh::lean_ctor_get(v_ictx_5547_, 0);
    crate::leanh::lean_inc_ref(v_ctx_5550_);
    v_info_5551_ = crate::leanh::lean_ctor_get(v_ictx_5547_, 1);
    crate::leanh::lean_inc_ref_n(v_info_5551_, 3);
    v_children_5552_ = crate::leanh::lean_ctor_get(v_ictx_5547_, 2);
    crate::leanh::lean_inc_ref(v_children_5552_);
    crate::leanh::lean_dec_ref(v_ictx_5547_);
    v___x_5553_ = crate::leanh::lean_box((v_kind_5546_) as usize);
    v___f_5554_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_locationLinksOfInfo___lam__0___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5554_, 0, v___x_5553_);
    v___y_5555_ = crate::leanh::lean_alloc_closure(
        l_Lean_Server_locationLinksOfInfo___lam__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___y_5555_, 0, v_info_5551_);
    crate::leanh::lean_closure_set(v___y_5555_, 1, v___f_5554_);
    v___x_5556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5556_, 0, v_info_5551_);
    v_ctx_5557_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
    crate::leanh::lean_ctor_set(v_ctx_5557_, 0, v_doc_5545_);
    crate::leanh::lean_ctor_set(v_ctx_5557_, 1, v_infoTree_x3f_5548_);
    crate::leanh::lean_ctor_set(v_ctx_5557_, 2, v___x_5556_);
    crate::leanh::lean_ctor_set(v_ctx_5557_, 3, v_children_5552_);
    crate::leanh::lean_ctor_set_uint8(
        v_ctx_5557_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v_kind_5546_,
    );
    v___x_5558_ = l_Lean_Elab_Info_lctx(v_info_5551_);
    crate::leanh::lean_dec_ref(v_info_5551_);
    v___x_5559_ =
        l_Lean_Server_GoToM_run___redArg(v_ctx_5557_, v_ctx_5550_, v___x_5558_, v___y_5555_);
    return v___x_5559_;
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo___boxed(
    mut v_doc_5560_: *mut crate::leanh::LeanObject,
    mut v_kind_5561_: *mut crate::leanh::LeanObject,
    mut v_ictx_5562_: *mut crate::leanh::LeanObject,
    mut v_infoTree_x3f_5563_: *mut crate::leanh::LeanObject,
    mut v_a_5564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_5565_: u8 = 0;
    let mut v_res_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5565_ = (crate::leanh::lean_unbox(v_kind_5561_) as u8);
    v_res_5566_ = l_Lean_Server_locationLinksOfInfo(
        v_doc_5560_,
        v_kind_boxed_5565_,
        v_ictx_5562_,
        v_infoTree_x3f_5563_,
    );
    return v_res_5566_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_GoTo(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Utils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Internal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_GoTo(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_GoTo(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Utils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Internal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_GoTo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_GoTo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_GoTo(builtin);
}
