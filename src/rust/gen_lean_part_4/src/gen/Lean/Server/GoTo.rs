// Lean compiler output
// Module: Lean.Server.GoTo
// Imports: Lean.Server.Utils Lean.Data.Lsp.Internal Lean.Util.CollectFVars Lean.Util.ForEachExpr Lean.Parser.Module
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get, lean_array_get_size, lean_array_push,
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv,
    lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub,
};
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
pub static l_Lean_Server_instBEqGoToKind___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Server_instBEqGoToKind_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Server_instBEqGoToKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instBEqGoToKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Server_instBEqGoToKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instBEqGoToKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__0_value:
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
    m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__2_value:
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
    m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__4_value:
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
    m_data: [116, 121, 112, 101, 0],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind_toJson___closed__5_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instToJsonGoToKind_toJson___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind_toJson___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instToJsonGoToKind___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Server_instToJsonGoToKind_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Server_instToJsonGoToKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Server_instToJsonGoToKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instToJsonGoToKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2_value:
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
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4_value:
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
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5_value:
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
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_instFromJsonGoToKind___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Server_instFromJsonGoToKind_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instFromJsonGoToKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Server_instFromJsonGoToKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instFromJsonGoToKind___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_GoToKind_determineTargetExprs___closed__2_value:
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
    m_fun: l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_GoToKind_determineTargetExprs___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_GoToKind_determineTargetExprs___closed__3_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Server_GoToKind_determineTargetExprs___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_GoToKind_determineTargetExprs___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Server_getInstanceProjectionArg_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_getInstanceProjectionArg_x3f___closed__0: u64 = 0;
static mut l_Lean_Server_getInstanceProjectionArg_x3f___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_getInstanceProjectionArg_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_locationLinksFromDecl___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_Server_locationLinksFromDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromDecl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__2_value:
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
    m_data: [77, 111, 100, 117, 108, 101, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__3_value:
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
    m_data: [105, 109, 112, 111, 114, 116, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        5561193377245250799 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        3187861556840815537 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__5_value:
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
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__7_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        5561193377245250799 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__8_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        9485984681193916779 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__9_value:
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
    m_data: [109, 101, 116, 97, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        5561193377245250799 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__10_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__9_value)
            as *mut leanh::LeanObject,
        17003524124175295577 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__11_value:
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
    m_data: [112, 117, 98, 108, 105, 99, 0],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        5561193377245250799 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Server_locationLinksFromImport___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__12_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        12460543829726897862 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_locationLinksFromImport___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [68, 101, 108, 97, 98, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__1_value) as *mut leanh::LeanObject,15682102345768914502 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 108, 97, 98, 65, 112, 112, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value) as *mut leanh::LeanObject,7892421401833366012 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__5_value) as *mut leanh::LeanObject,6086138408723263506 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_locationLinksFromImport___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__3_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__4_value) as *mut leanh::LeanObject,7892421401833366012 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__7_value) as *mut leanh::LeanObject,252081343774567219 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Server_GoToKind_ctorIdx(mut v_x_2784_: u8) -> *mut leanh::LeanObject {
    match v_x_2784_ {
        0 => {
            let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2785_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2785_;
        }
        1 => {
            let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2786_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2786_;
        }
        _ => {
            let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2787_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2787_;
        }
    }
}
pub unsafe fn l_Lean_Server_GoToKind_ctorIdx___boxed(
    mut v_x_2788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2789_: u8 = 0;
    let mut v_res_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2789_ = (leanh::lean_unbox(v_x_2788_) as u8);
    v_res_2790_ = l_Lean_Server_GoToKind_ctorIdx(v_x_boxed_2789_);
    return v_res_2790_;
}
pub unsafe fn l_Lean_Server_GoToKind_toCtorIdx(mut v_x_2791_: u8) -> *mut leanh::LeanObject {
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2792_ = l_Lean_Server_GoToKind_ctorIdx(v_x_2791_);
    return v___x_2792_;
}
pub unsafe fn l_Lean_Server_GoToKind_toCtorIdx___boxed(
    mut v_x_2793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_2794_: u8 = 0;
    let mut v_res_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2794_ = (leanh::lean_unbox(v_x_2793_) as u8);
    v_res_2795_ = l_Lean_Server_GoToKind_toCtorIdx(v_x_4__boxed_2794_);
    return v_res_2795_;
}
pub unsafe fn l_Lean_Server_GoToKind_ctorElim___redArg(
    mut v_k_2796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2796_);
    return v_k_2796_;
}
pub unsafe fn l_Lean_Server_GoToKind_ctorElim___redArg___boxed(
    mut v_k_2797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Lean_Server_GoToKind_ctorElim___redArg(v_k_2797_);
    leanh::lean_dec(v_k_2797_);
    return v_res_2798_;
}
pub unsafe fn l_Lean_Server_GoToKind_ctorElim(
    mut v_motive_2799_: *mut leanh::LeanObject,
    mut v_ctorIdx_2800_: *mut leanh::LeanObject,
    mut v_t_2801_: u8,
    mut v_h_2802_: *mut leanh::LeanObject,
    mut v_k_2803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2803_);
    return v_k_2803_;
}
pub unsafe fn l_Lean_Server_GoToKind_ctorElim___boxed(
    mut v_motive_2804_: *mut leanh::LeanObject,
    mut v_ctorIdx_2805_: *mut leanh::LeanObject,
    mut v_t_2806_: *mut leanh::LeanObject,
    mut v_h_2807_: *mut leanh::LeanObject,
    mut v_k_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2809_: u8 = 0;
    let mut v_res_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2809_ = (leanh::lean_unbox(v_t_2806_) as u8);
    v_res_2810_ = l_Lean_Server_GoToKind_ctorElim(
        v_motive_2804_,
        v_ctorIdx_2805_,
        v_t_boxed_2809_,
        v_h_2807_,
        v_k_2808_,
    );
    leanh::lean_dec(v_k_2808_);
    leanh::lean_dec(v_ctorIdx_2805_);
    return v_res_2810_;
}
pub unsafe fn l_Lean_Server_GoToKind_declaration_elim___redArg(
    mut v_declaration_2811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_declaration_2811_);
    return v_declaration_2811_;
}
pub unsafe fn l_Lean_Server_GoToKind_declaration_elim___redArg___boxed(
    mut v_declaration_2812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2813_ = l_Lean_Server_GoToKind_declaration_elim___redArg(v_declaration_2812_);
    leanh::lean_dec(v_declaration_2812_);
    return v_res_2813_;
}
pub unsafe fn l_Lean_Server_GoToKind_declaration_elim(
    mut v_motive_2814_: *mut leanh::LeanObject,
    mut v_t_2815_: u8,
    mut v_h_2816_: *mut leanh::LeanObject,
    mut v_declaration_2817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_declaration_2817_);
    return v_declaration_2817_;
}
pub unsafe fn l_Lean_Server_GoToKind_declaration_elim___boxed(
    mut v_motive_2818_: *mut leanh::LeanObject,
    mut v_t_2819_: *mut leanh::LeanObject,
    mut v_h_2820_: *mut leanh::LeanObject,
    mut v_declaration_2821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2822_: u8 = 0;
    let mut v_res_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2822_ = (leanh::lean_unbox(v_t_2819_) as u8);
    v_res_2823_ = l_Lean_Server_GoToKind_declaration_elim(
        v_motive_2818_,
        v_t_boxed_2822_,
        v_h_2820_,
        v_declaration_2821_,
    );
    leanh::lean_dec(v_declaration_2821_);
    return v_res_2823_;
}
pub unsafe fn l_Lean_Server_GoToKind_definition_elim___redArg(
    mut v_definition_2824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_definition_2824_);
    return v_definition_2824_;
}
pub unsafe fn l_Lean_Server_GoToKind_definition_elim___redArg___boxed(
    mut v_definition_2825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2826_ = l_Lean_Server_GoToKind_definition_elim___redArg(v_definition_2825_);
    leanh::lean_dec(v_definition_2825_);
    return v_res_2826_;
}
pub unsafe fn l_Lean_Server_GoToKind_definition_elim(
    mut v_motive_2827_: *mut leanh::LeanObject,
    mut v_t_2828_: u8,
    mut v_h_2829_: *mut leanh::LeanObject,
    mut v_definition_2830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_definition_2830_);
    return v_definition_2830_;
}
pub unsafe fn l_Lean_Server_GoToKind_definition_elim___boxed(
    mut v_motive_2831_: *mut leanh::LeanObject,
    mut v_t_2832_: *mut leanh::LeanObject,
    mut v_h_2833_: *mut leanh::LeanObject,
    mut v_definition_2834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2835_: u8 = 0;
    let mut v_res_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2835_ = (leanh::lean_unbox(v_t_2832_) as u8);
    v_res_2836_ = l_Lean_Server_GoToKind_definition_elim(
        v_motive_2831_,
        v_t_boxed_2835_,
        v_h_2833_,
        v_definition_2834_,
    );
    leanh::lean_dec(v_definition_2834_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_Server_GoToKind_type_elim___redArg(
    mut v_type_2837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_type_2837_);
    return v_type_2837_;
}
pub unsafe fn l_Lean_Server_GoToKind_type_elim___redArg___boxed(
    mut v_type_2838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2839_ = l_Lean_Server_GoToKind_type_elim___redArg(v_type_2838_);
    leanh::lean_dec(v_type_2838_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_Server_GoToKind_type_elim(
    mut v_motive_2840_: *mut leanh::LeanObject,
    mut v_t_2841_: u8,
    mut v_h_2842_: *mut leanh::LeanObject,
    mut v_type_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_type_2843_);
    return v_type_2843_;
}
pub unsafe fn l_Lean_Server_GoToKind_type_elim___boxed(
    mut v_motive_2844_: *mut leanh::LeanObject,
    mut v_t_2845_: *mut leanh::LeanObject,
    mut v_h_2846_: *mut leanh::LeanObject,
    mut v_type_2847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2848_: u8 = 0;
    let mut v_res_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2848_ = (leanh::lean_unbox(v_t_2845_) as u8);
    v_res_2849_ =
        l_Lean_Server_GoToKind_type_elim(v_motive_2844_, v_t_boxed_2848_, v_h_2846_, v_type_2847_);
    leanh::lean_dec(v_type_2847_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Server_instBEqGoToKind_beq(mut v_x_2850_: u8, mut v_y_2851_: u8) -> u8 {
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u8 = 0;
    v___x_2852_ = l_Lean_Server_GoToKind_ctorIdx(v_x_2850_);
    v___x_2853_ = l_Lean_Server_GoToKind_ctorIdx(v_y_2851_);
    v___x_2854_ = lean_nat_dec_eq(v___x_2852_, v___x_2853_);
    leanh::lean_dec(v___x_2853_);
    leanh::lean_dec(v___x_2852_);
    return v___x_2854_;
}
pub unsafe fn l_Lean_Server_instBEqGoToKind_beq___boxed(
    mut v_x_2855_: *mut leanh::LeanObject,
    mut v_y_2856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_2857_: u8 = 0;
    let mut v_y_18__boxed_2858_: u8 = 0;
    let mut v_res_2859_: u8 = 0;
    let mut v_r_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2857_ = (leanh::lean_unbox(v_x_2855_) as u8);
    v_y_18__boxed_2858_ = (leanh::lean_unbox(v_y_2856_) as u8);
    v_res_2859_ = l_Lean_Server_instBEqGoToKind_beq(v_x_17__boxed_2857_, v_y_18__boxed_2858_);
    v_r_2860_ = leanh::lean_box((v_res_2859_) as usize);
    return v_r_2860_;
}
pub unsafe fn l_Lean_Server_instToJsonGoToKind_toJson(
    mut v_x_2872_: u8,
) -> *mut leanh::LeanObject {
    match v_x_2872_ {
        0 => {
            let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2873_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__1;
            return v___x_2873_;
        }
        1 => {
            let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2874_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__3;
            return v___x_2874_;
        }
        _ => {
            let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2875_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__5;
            return v___x_2875_;
        }
    }
}
pub unsafe fn l_Lean_Server_instToJsonGoToKind_toJson___boxed(
    mut v_x_2876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_67__boxed_2877_: u8 = 0;
    let mut v_res_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_67__boxed_2877_ = (leanh::lean_unbox(v_x_2876_) as u8);
    v_res_2878_ = l_Lean_Server_instToJsonGoToKind_toJson(v_x_67__boxed_2877_);
    return v_res_2878_;
}
pub unsafe fn l_Lean_Server_instFromJsonGoToKind_fromJson(
    mut v_json_2896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2897_ = l_Lean_Json_getTag_x3f(v_json_2896_);
    if leanh::lean_obj_tag(v___x_2897_) == 0 {
        let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2898_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__1;
        return v___x_2898_;
    } else {
        let mut v_val_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2901_: u8 = 0;
        v_val_2899_ = leanh::lean_ctor_get(v___x_2897_, 0);
        leanh::lean_inc(v_val_2899_);
        leanh::lean_dec_ref_known(v___x_2897_, 1);
        v___x_2900_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__4;
        v___x_2901_ = lean_string_dec_eq(v_val_2899_, v___x_2900_);
        if v___x_2901_ == 0 {
            let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2903_: u8 = 0;
            v___x_2902_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__0;
            v___x_2903_ = lean_string_dec_eq(v_val_2899_, v___x_2902_);
            if v___x_2903_ == 0 {
                let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2905_: u8 = 0;
                v___x_2904_ = l_Lean_Server_instToJsonGoToKind_toJson___closed__2;
                v___x_2905_ = lean_string_dec_eq(v_val_2899_, v___x_2904_);
                leanh::lean_dec(v_val_2899_);
                if v___x_2905_ == 0 {
                    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2906_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__3;
                    return v___x_2906_;
                } else {
                    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2907_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__4;
                    return v___x_2907_;
                }
            } else {
                let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_val_2899_);
                v___x_2908_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__5;
                return v___x_2908_;
            }
        } else {
            let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_2899_);
            v___x_2909_ = l_Lean_Server_instFromJsonGoToKind_fromJson___closed__6;
            return v___x_2909_;
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(
    mut v_e_2912_: *mut leanh::LeanObject,
    mut v___y_2913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_unused_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2915_ = l_Lean_Expr_hasMVar(v_e_2912_);
                if v___x_2915_ == 0 {
                    v___x_2916_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2916_, 0, v_e_2912_);
                    return v___x_2916_;
                } else {
                    v___x_2917_ = lean_st_ref_get(v___y_2913_);
                    v_mctx_2918_ = leanh::lean_ctor_get(v___x_2917_, 0);
                    leanh::lean_inc_ref(v_mctx_2918_);
                    leanh::lean_dec(v___x_2917_);
                    v___x_2919_ = l_Lean_instantiateMVarsCore(v_mctx_2918_, v_e_2912_);
                    v_fst_2920_ = leanh::lean_ctor_get(v___x_2919_, 0);
                    leanh::lean_inc(v_fst_2920_);
                    v_snd_2921_ = leanh::lean_ctor_get(v___x_2919_, 1);
                    leanh::lean_inc(v_snd_2921_);
                    leanh::lean_dec_ref(v___x_2919_);
                    v___x_2922_ = lean_st_ref_take(v___y_2913_);
                    v_cache_2923_ = leanh::lean_ctor_get(v___x_2922_, 1);
                    v_zetaDeltaFVarIds_2924_ = leanh::lean_ctor_get(v___x_2922_, 2);
                    v_postponed_2925_ = leanh::lean_ctor_get(v___x_2922_, 3);
                    v_diag_2926_ = leanh::lean_ctor_get(v___x_2922_, 4);
                    v_isSharedCheck_2935_ = (!leanh::lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2935_ == 0 {
                        v_unused_2936_ = leanh::lean_ctor_get(v___x_2922_, 0);
                        leanh::lean_dec(v_unused_2936_);
                        v___x_2928_ = v___x_2922_;
                        v_isShared_2929_ = v_isSharedCheck_2935_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_2926_);
                        leanh::lean_inc(v_postponed_2925_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_2924_);
                        leanh::lean_inc(v_cache_2923_);
                        leanh::lean_dec(v___x_2922_);
                        v___x_2928_ = leanh::lean_box(0);
                        v_isShared_2929_ = v_isSharedCheck_2935_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2929_ == 0 {
                    leanh::lean_ctor_set(v___x_2928_, 0, v_snd_2921_);
                    v___x_2931_ = v___x_2928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_snd_2921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_cache_2923_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2934_,
                        2,
                        v_zetaDeltaFVarIds_2924_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 3, v_postponed_2925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 4, v_diag_2926_);
                    v___x_2931_ = v_reuseFailAlloc_2934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2932_ = lean_st_ref_set(v___y_2913_, v___x_2931_);
                v___x_2933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2933_, 0, v_fst_2920_);
                return v___x_2933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg___boxed(
    mut v_e_2937_: *mut leanh::LeanObject,
    mut v___y_2938_: *mut leanh::LeanObject,
    mut v___y_2939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ =
        l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(
            v_e_2937_,
            v___y_2938_,
        );
    leanh::lean_dec(v___y_2938_);
    return v_res_2940_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(
    mut v_e_2941_: *mut leanh::LeanObject,
    mut v___y_2942_: *mut leanh::LeanObject,
    mut v___y_2943_: *mut leanh::LeanObject,
    mut v___y_2944_: *mut leanh::LeanObject,
    mut v___y_2945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ =
        l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(
            v_e_2941_,
            v___y_2943_,
        );
    return v___x_2947_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___boxed(
    mut v_e_2948_: *mut leanh::LeanObject,
    mut v___y_2949_: *mut leanh::LeanObject,
    mut v___y_2950_: *mut leanh::LeanObject,
    mut v___y_2951_: *mut leanh::LeanObject,
    mut v___y_2952_: *mut leanh::LeanObject,
    mut v___y_2953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2954_ =
        l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0(
            v_e_2948_,
            v___y_2949_,
            v___y_2950_,
            v___y_2951_,
            v___y_2952_,
        );
    leanh::lean_dec(v___y_2952_);
    leanh::lean_dec_ref(v___y_2951_);
    leanh::lean_dec(v___y_2950_);
    leanh::lean_dec_ref(v___y_2949_);
    return v_res_2954_;
}
pub unsafe fn l_Lean_Server_GoToKind_determineTargetExprs___lam__0(
    mut v_e_2955_: *mut leanh::LeanObject,
    mut v___y_2956_: *mut leanh::LeanObject,
    mut v___y_2957_: *mut leanh::LeanObject,
    mut v___y_2958_: *mut leanh::LeanObject,
    mut v___y_2959_: *mut leanh::LeanObject,
    mut v___y_2960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_2955_) {
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
                    leanh::lean_dec_ref(v_e_2955_);
                    v_snd_2963_ = v___y_2956_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_2964_ = 1;
                v___x_2965_ = leanh::lean_box((v___x_2964_) as usize);
                v___x_2966_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2966_, 0, v___x_2965_);
                leanh::lean_ctor_set(v___x_2966_, 1, v_snd_2963_);
                v___x_2967_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2967_, 0, v___x_2966_);
                return v___x_2967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_GoToKind_determineTargetExprs___lam__0___boxed(
    mut v_e_2970_: *mut leanh::LeanObject,
    mut v___y_2971_: *mut leanh::LeanObject,
    mut v___y_2972_: *mut leanh::LeanObject,
    mut v___y_2973_: *mut leanh::LeanObject,
    mut v___y_2974_: *mut leanh::LeanObject,
    mut v___y_2975_: *mut leanh::LeanObject,
    mut v___y_2976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2977_ = l_Lean_Server_GoToKind_determineTargetExprs___lam__0(
        v_e_2970_,
        v___y_2971_,
        v___y_2972_,
        v___y_2973_,
        v___y_2974_,
        v___y_2975_,
    );
    leanh::lean_dec(v___y_2975_);
    leanh::lean_dec_ref(v___y_2974_);
    leanh::lean_dec(v___y_2973_);
    leanh::lean_dec_ref(v___y_2972_);
    return v_res_2977_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(
    mut v_a_2978_: *mut leanh::LeanObject,
    mut v_b_2979_: *mut leanh::LeanObject,
    mut v_x_2980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2980_) == 0 {
                    leanh::lean_dec(v_b_2979_);
                    leanh::lean_dec_ref(v_a_2978_);
                    return v_x_2980_;
                } else {
                    v_key_2981_ = leanh::lean_ctor_get(v_x_2980_, 0);
                    v_value_2982_ = leanh::lean_ctor_get(v_x_2980_, 1);
                    v_tail_2983_ = leanh::lean_ctor_get(v_x_2980_, 2);
                    v_isSharedCheck_2995_ = (!leanh::lean_is_exclusive(v_x_2980_)) as u8;
                    if v_isSharedCheck_2995_ == 0 {
                        v___x_2985_ = v_x_2980_;
                        v_isShared_2986_ = v_isSharedCheck_2995_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2983_);
                        leanh::lean_inc(v_value_2982_);
                        leanh::lean_inc(v_key_2981_);
                        leanh::lean_dec(v_x_2980_);
                        v___x_2985_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_2985_, 2, v___x_2988_);
                        v___x_2990_ = v___x_2985_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2991_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_key_2981_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_value_2982_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 2, v___x_2988_);
                        v___x_2990_ = v_reuseFailAlloc_2991_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_2982_);
                    leanh::lean_dec(v_key_2981_);
                    if v_isShared_2986_ == 0 {
                        leanh::lean_ctor_set(v___x_2985_, 1, v_b_2979_);
                        leanh::lean_ctor_set(v___x_2985_, 0, v_a_2978_);
                        v___x_2993_ = v___x_2985_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2994_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2978_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_b_2979_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_tail_2983_);
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
    mut v_a_2996_: *mut leanh::LeanObject,
    mut v_x_2997_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2998_: u8 = 0;
    let mut v_key_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2997_) == 0 {
                    v___x_2998_ = 0;
                    return v___x_2998_;
                } else {
                    v_key_2999_ = leanh::lean_ctor_get(v_x_2997_, 0);
                    v_tail_3000_ = leanh::lean_ctor_get(v_x_2997_, 2);
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
    mut v_a_3003_: *mut leanh::LeanObject,
    mut v_x_3004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3005_: u8 = 0;
    let mut v_r_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3005_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_3003_, v_x_3004_);
    leanh::lean_dec(v_x_3004_);
    leanh::lean_dec_ref(v_a_3003_);
    v_r_3006_ = leanh::lean_box((v_res_3005_) as usize);
    return v_r_3006_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(
    mut v_x_3007_: *mut leanh::LeanObject,
    mut v_x_3008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3014_: u8 = 0;
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3008_) == 0 {
                    return v_x_3007_;
                } else {
                    v_key_3009_ = leanh::lean_ctor_get(v_x_3008_, 0);
                    v_value_3010_ = leanh::lean_ctor_get(v_x_3008_, 1);
                    v_tail_3011_ = leanh::lean_ctor_get(v_x_3008_, 2);
                    v_isSharedCheck_3034_ = (!leanh::lean_is_exclusive(v_x_3008_)) as u8;
                    if v_isSharedCheck_3034_ == 0 {
                        v___x_3013_ = v_x_3008_;
                        v_isShared_3014_ = v_isSharedCheck_3034_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3011_);
                        leanh::lean_inc(v_value_3010_);
                        leanh::lean_inc(v_key_3009_);
                        leanh::lean_dec(v_x_3008_);
                        v___x_3013_ = leanh::lean_box(0);
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
                leanh::lean_inc(v___x_3028_);
                if v_isShared_3014_ == 0 {
                    leanh::lean_ctor_set(v___x_3013_, 2, v___x_3028_);
                    v___x_3030_ = v___x_3013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_key_3009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_value_3010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 2, v___x_3028_);
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
    mut v_i_3035_: *mut leanh::LeanObject,
    mut v_source_3036_: *mut leanh::LeanObject,
    mut v_target_3037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v_es_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3038_ = lean_array_get_size(v_source_3036_);
                v___x_3039_ = lean_nat_dec_lt(v_i_3035_, v___x_3038_);
                if v___x_3039_ == 0 {
                    leanh::lean_dec_ref(v_source_3036_);
                    leanh::lean_dec(v_i_3035_);
                    return v_target_3037_;
                } else {
                    v_es_3040_ = lean_array_fget(v_source_3036_, v_i_3035_);
                    v___x_3041_ = leanh::lean_box(0);
                    v_source_3042_ = lean_array_fset(v_source_3036_, v_i_3035_, v___x_3041_);
                    v_target_3043_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_target_3037_, v_es_3040_);
                    v___x_3044_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3045_ = lean_nat_add(v_i_3035_, v___x_3044_);
                    leanh::lean_dec(v_i_3035_);
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
    mut v_data_3047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = lean_array_get_size(v_data_3047_);
    v___x_3049_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3050_ = lean_nat_mul(v___x_3048_, v___x_3049_);
    v___x_3051_ = leanh::lean_unsigned_to_nat(0);
    v___x_3052_ = leanh::lean_box(0);
    v___x_3053_ = lean_mk_array(v_nbuckets_3050_, v___x_3052_);
    v___x_3054_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v___x_3051_, v_data_3047_, v___x_3053_);
    return v___x_3054_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(
    mut v_m_3055_: *mut leanh::LeanObject,
    mut v_a_3056_: *mut leanh::LeanObject,
    mut v_b_3057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: u8 = 0;
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v_val_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3058_ = leanh::lean_ctor_get(v_m_3055_, 0);
                v_buckets_3059_ = leanh::lean_ctor_get(v_m_3055_, 1);
                v_isSharedCheck_3102_ = (!leanh::lean_is_exclusive(v_m_3055_)) as u8;
                if v_isSharedCheck_3102_ == 0 {
                    v___x_3061_ = v_m_3055_;
                    v_isShared_3062_ = v_isSharedCheck_3102_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3059_);
                    leanh::lean_inc(v_size_3058_);
                    leanh::lean_dec(v_m_3055_);
                    v___x_3061_ = leanh::lean_box(0);
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
                    v___x_3078_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3079_ = lean_nat_add(v_size_3058_, v___x_3078_);
                    leanh::lean_dec(v_size_3058_);
                    leanh::lean_inc(v_bkt_3076_);
                    v___x_3080_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3080_, 0, v_a_3056_);
                    leanh::lean_ctor_set(v___x_3080_, 1, v_b_3057_);
                    leanh::lean_ctor_set(v___x_3080_, 2, v_bkt_3076_);
                    v_buckets_x27_3081_ =
                        lean_array_uset(v_buckets_3059_, v___x_3075_, v___x_3080_);
                    v___x_3082_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3083_ = lean_nat_mul(v_size_x27_3079_, v___x_3082_);
                    v___x_3084_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3085_ = lean_nat_div(v___x_3083_, v___x_3084_);
                    leanh::lean_dec(v___x_3083_);
                    v___x_3086_ = lean_array_get_size(v_buckets_x27_3081_);
                    v___x_3087_ = lean_nat_dec_le(v___x_3085_, v___x_3086_);
                    leanh::lean_dec(v___x_3085_);
                    if v___x_3087_ == 0 {
                        v_val_3088_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_buckets_x27_3081_);
                        if v_isShared_3062_ == 0 {
                            leanh::lean_ctor_set(v___x_3061_, 1, v_val_3088_);
                            leanh::lean_ctor_set(v___x_3061_, 0, v_size_x27_3079_);
                            v___x_3090_ = v___x_3061_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3091_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3091_,
                                0,
                                v_size_x27_3079_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_val_3088_);
                            v___x_3090_ = v_reuseFailAlloc_3091_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3062_ == 0 {
                            leanh::lean_ctor_set(v___x_3061_, 1, v_buckets_x27_3081_);
                            leanh::lean_ctor_set(v___x_3061_, 0, v_size_x27_3079_);
                            v___x_3093_ = v___x_3061_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3094_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3094_,
                                0,
                                v_size_x27_3079_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_3076_);
                    v___x_3095_ = leanh::lean_box(0);
                    v_buckets_x27_3096_ =
                        lean_array_uset(v_buckets_3059_, v___x_3075_, v___x_3095_);
                    v___x_3097_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_3056_, v_b_3057_, v_bkt_3076_);
                    v___x_3098_ = lean_array_uset(v_buckets_x27_3096_, v___x_3075_, v___x_3097_);
                    if v_isShared_3062_ == 0 {
                        leanh::lean_ctor_set(v___x_3061_, 1, v___x_3098_);
                        v___x_3100_ = v___x_3061_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3101_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_size_3058_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3098_);
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
    mut v_a_3103_: *mut leanh::LeanObject,
    mut v_x_3104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3104_) == 0 {
                    v___x_3105_ = leanh::lean_box(0);
                    return v___x_3105_;
                } else {
                    v_key_3106_ = leanh::lean_ctor_get(v_x_3104_, 0);
                    v_value_3107_ = leanh::lean_ctor_get(v_x_3104_, 1);
                    v_tail_3108_ = leanh::lean_ctor_get(v_x_3104_, 2);
                    v___x_3109_ = lean_expr_eqv(v_key_3106_, v_a_3103_);
                    if v___x_3109_ == 0 {
                        v_x_3104_ = v_tail_3108_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3107_);
                        v___x_3111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3111_, 0, v_value_3107_);
                        return v___x_3111_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_a_3112_: *mut leanh::LeanObject,
    mut v_x_3113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3114_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_3112_, v_x_3113_);
    leanh::lean_dec(v_x_3113_);
    leanh::lean_dec_ref(v_a_3112_);
    return v_res_3114_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(
    mut v_m_3115_: *mut leanh::LeanObject,
    mut v_a_3116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3117_ = leanh::lean_ctor_get(v_m_3115_, 1);
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
    mut v_m_3133_: *mut leanh::LeanObject,
    mut v_a_3134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_3133_, v_a_3134_);
    leanh::lean_dec_ref(v_a_3134_);
    leanh::lean_dec_ref(v_m_3133_);
    return v_res_3135_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(
    mut v_g_3136_: *mut leanh::LeanObject,
    mut v_e_3137_: *mut leanh::LeanObject,
    mut v_a_3138_: *mut leanh::LeanObject,
    mut v___y_3139_: *mut leanh::LeanObject,
    mut v___y_3140_: *mut leanh::LeanObject,
    mut v___y_3141_: *mut leanh::LeanObject,
    mut v___y_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v_d_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3206_: u8 = 0;
    let mut v_a_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut v_val_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3156_ = lean_st_ref_get(v_a_3138_);
                v___x_3157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v___x_3156_, v_e_3137_);
                leanh::lean_dec(v___x_3156_);
                if leanh::lean_obj_tag(v___x_3157_) == 0 {
                    leanh::lean_inc_ref(v_g_3136_);
                    leanh::lean_inc(v___y_3143_);
                    leanh::lean_inc_ref(v___y_3142_);
                    leanh::lean_inc(v___y_3141_);
                    leanh::lean_inc_ref(v___y_3140_);
                    leanh::lean_inc_ref(v_e_3137_);
                    v___x_3158_ = leanh::lean_apply_7(
                        v_g_3136_,
                        v_e_3137_,
                        v___y_3139_,
                        v___y_3140_,
                        v___y_3141_,
                        v___y_3142_,
                        v___y_3143_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3158_) == 0 {
                        v_a_3159_ = leanh::lean_ctor_get(v___x_3158_, 0);
                        leanh::lean_inc(v_a_3159_);
                        leanh::lean_dec_ref_known(v___x_3158_, 1);
                        v_fst_3160_ = leanh::lean_ctor_get(v_a_3159_, 0);
                        v_snd_3161_ = leanh::lean_ctor_get(v_a_3159_, 1);
                        v_isSharedCheck_3206_ = (!leanh::lean_is_exclusive(v_a_3159_)) as u8;
                        if v_isSharedCheck_3206_ == 0 {
                            v___x_3163_ = v_a_3159_;
                            v_isShared_3164_ = v_isSharedCheck_3206_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3161_);
                            leanh::lean_inc(v_fst_3160_);
                            leanh::lean_dec(v_a_3159_);
                            v___x_3163_ = leanh::lean_box(0);
                            v_isShared_3164_ = v_isSharedCheck_3206_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_3137_);
                        leanh::lean_dec_ref(v_g_3136_);
                        v_a_3207_ = leanh::lean_ctor_get(v___x_3158_, 0);
                        v_isSharedCheck_3214_ =
                            (!leanh::lean_is_exclusive(v___x_3158_)) as u8;
                        if v_isSharedCheck_3214_ == 0 {
                            v___x_3209_ = v___x_3158_;
                            v_isShared_3210_ = v_isSharedCheck_3214_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3207_);
                            leanh::lean_dec(v___x_3158_);
                            v___x_3209_ = leanh::lean_box(0);
                            v_isShared_3210_ = v_isSharedCheck_3214_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3137_);
                    leanh::lean_dec_ref(v_g_3136_);
                    v_val_3215_ = leanh::lean_ctor_get(v___x_3157_, 0);
                    v_isSharedCheck_3223_ = (!leanh::lean_is_exclusive(v___x_3157_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3217_ = v___x_3157_;
                        v_isShared_3218_ = v_isSharedCheck_3223_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3215_);
                        leanh::lean_dec(v___x_3157_);
                        v___x_3217_ = leanh::lean_box(0);
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
                v___x_3151_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3151_, 0, v_a_3146_);
                return v___x_3151_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_3153_) == 0 {
                    v_a_3154_ = leanh::lean_ctor_get(v___y_3153_, 0);
                    leanh::lean_inc(v_a_3154_);
                    leanh::lean_dec_ref_known(v___y_3153_, 1);
                    v_fst_3155_ = leanh::lean_ctor_get(v_a_3154_, 0);
                    leanh::lean_inc(v_fst_3155_);
                    v_a_3146_ = v_a_3154_;
                    v_fst_3147_ = v_fst_3155_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_3137_);
                    return v___y_3153_;
                }
            }
            3 => {
                v___x_3173_ = (leanh::lean_unbox(v_fst_3160_) as u8);
                leanh::lean_dec(v_fst_3160_);
                if v___x_3173_ == 0 {
                    leanh::lean_dec_ref(v_g_3136_);
                    v___x_3174_ = leanh::lean_box(0);
                    if v_isShared_3164_ == 0 {
                        leanh::lean_ctor_set(v___x_3163_, 0, v___x_3174_);
                        v___x_3176_ = v___x_3163_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3177_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_snd_3161_);
                        v___x_3176_ = v_reuseFailAlloc_3177_;
                        state = 5;
                        continue;
                    }
                } else {
                    match leanh::lean_obj_tag(v_e_3137_) {
                        7 => {
                            leanh::lean_del_object(v___x_3163_);
                            v_binderType_3178_ = leanh::lean_ctor_get(v_e_3137_, 1);
                            v_body_3179_ = leanh::lean_ctor_get(v_e_3137_, 2);
                            leanh::lean_inc_ref(v_body_3179_);
                            leanh::lean_inc_ref(v_binderType_3178_);
                            v_d_3166_ = v_binderType_3178_;
                            v_b_3167_ = v_body_3179_;
                            v___y_3168_ = v_a_3138_;
                            state = 4;
                            continue;
                        }
                        6 => {
                            leanh::lean_del_object(v___x_3163_);
                            v_binderType_3180_ = leanh::lean_ctor_get(v_e_3137_, 1);
                            v_body_3181_ = leanh::lean_ctor_get(v_e_3137_, 2);
                            leanh::lean_inc_ref(v_body_3181_);
                            leanh::lean_inc_ref(v_binderType_3180_);
                            v_d_3166_ = v_binderType_3180_;
                            v_b_3167_ = v_body_3181_;
                            v___y_3168_ = v_a_3138_;
                            state = 4;
                            continue;
                        }
                        8 => {
                            leanh::lean_del_object(v___x_3163_);
                            v_type_3182_ = leanh::lean_ctor_get(v_e_3137_, 1);
                            v_value_3183_ = leanh::lean_ctor_get(v_e_3137_, 2);
                            v_body_3184_ = leanh::lean_ctor_get(v_e_3137_, 3);
                            leanh::lean_inc_ref(v_type_3182_);
                            leanh::lean_inc_ref(v_g_3136_);
                            v___x_3185_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_type_3182_, v_a_3138_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                            if leanh::lean_obj_tag(v___x_3185_) == 0 {
                                v_a_3186_ = leanh::lean_ctor_get(v___x_3185_, 0);
                                leanh::lean_inc(v_a_3186_);
                                leanh::lean_dec_ref_known(v___x_3185_, 1);
                                v_snd_3187_ = leanh::lean_ctor_get(v_a_3186_, 1);
                                leanh::lean_inc(v_snd_3187_);
                                leanh::lean_dec(v_a_3186_);
                                leanh::lean_inc_ref(v_value_3183_);
                                leanh::lean_inc_ref(v_g_3136_);
                                v___x_3188_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_value_3183_, v_a_3138_, v_snd_3187_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                                if leanh::lean_obj_tag(v___x_3188_) == 0 {
                                    v_a_3189_ = leanh::lean_ctor_get(v___x_3188_, 0);
                                    leanh::lean_inc(v_a_3189_);
                                    leanh::lean_dec_ref_known(v___x_3188_, 1);
                                    v_snd_3190_ = leanh::lean_ctor_get(v_a_3189_, 1);
                                    leanh::lean_inc(v_snd_3190_);
                                    leanh::lean_dec(v_a_3189_);
                                    leanh::lean_inc_ref(v_body_3184_);
                                    v___x_3191_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_body_3184_, v_a_3138_, v_snd_3190_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                                    v___y_3153_ = v___x_3191_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_g_3136_);
                                    v___y_3153_ = v___x_3188_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_g_3136_);
                                v___y_3153_ = v___x_3185_;
                                state = 2;
                                continue;
                            }
                        }
                        5 => {
                            leanh::lean_del_object(v___x_3163_);
                            v_fn_3192_ = leanh::lean_ctor_get(v_e_3137_, 0);
                            v_arg_3193_ = leanh::lean_ctor_get(v_e_3137_, 1);
                            leanh::lean_inc_ref(v_fn_3192_);
                            leanh::lean_inc_ref(v_g_3136_);
                            v___x_3194_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_fn_3192_, v_a_3138_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                            if leanh::lean_obj_tag(v___x_3194_) == 0 {
                                v_a_3195_ = leanh::lean_ctor_get(v___x_3194_, 0);
                                leanh::lean_inc(v_a_3195_);
                                leanh::lean_dec_ref_known(v___x_3194_, 1);
                                v_snd_3196_ = leanh::lean_ctor_get(v_a_3195_, 1);
                                leanh::lean_inc(v_snd_3196_);
                                leanh::lean_dec(v_a_3195_);
                                leanh::lean_inc_ref(v_arg_3193_);
                                v___x_3197_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_arg_3193_, v_a_3138_, v_snd_3196_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                                v___y_3153_ = v___x_3197_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_g_3136_);
                                v___y_3153_ = v___x_3194_;
                                state = 2;
                                continue;
                            }
                        }
                        10 => {
                            leanh::lean_del_object(v___x_3163_);
                            v_expr_3198_ = leanh::lean_ctor_get(v_e_3137_, 1);
                            leanh::lean_inc_ref(v_expr_3198_);
                            v___x_3199_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_expr_3198_, v_a_3138_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                            v___y_3153_ = v___x_3199_;
                            state = 2;
                            continue;
                        }
                        11 => {
                            leanh::lean_del_object(v___x_3163_);
                            v_struct_3200_ = leanh::lean_ctor_get(v_e_3137_, 2);
                            leanh::lean_inc_ref(v_struct_3200_);
                            v___x_3201_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_struct_3200_, v_a_3138_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                            v___y_3153_ = v___x_3201_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_g_3136_);
                            v___x_3202_ = leanh::lean_box(0);
                            if v_isShared_3164_ == 0 {
                                leanh::lean_ctor_set(v___x_3163_, 0, v___x_3202_);
                                v___x_3204_ = v___x_3163_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_3205_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_snd_3161_);
                                v___x_3204_ = v_reuseFailAlloc_3205_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                leanh::lean_inc_ref(v_g_3136_);
                v___x_3169_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_d_3166_, v___y_3168_, v_snd_3161_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                if leanh::lean_obj_tag(v___x_3169_) == 0 {
                    v_a_3170_ = leanh::lean_ctor_get(v___x_3169_, 0);
                    leanh::lean_inc(v_a_3170_);
                    leanh::lean_dec_ref_known(v___x_3169_, 1);
                    v_snd_3171_ = leanh::lean_ctor_get(v_a_3170_, 1);
                    leanh::lean_inc(v_snd_3171_);
                    leanh::lean_dec(v_a_3170_);
                    v___x_3172_ = l_Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1(v_g_3136_, v_b_3167_, v___y_3168_, v_snd_3171_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
                    v___y_3153_ = v___x_3172_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_3167_);
                    leanh::lean_dec_ref(v_g_3136_);
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
                    v_reuseFailAlloc_3213_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
                    v___x_3212_ = v_reuseFailAlloc_3213_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3212_;
            }
            9 => {
                v___x_3219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3219_, 0, v_val_3215_);
                leanh::lean_ctor_set(v___x_3219_, 1, v___y_3139_);
                if v_isShared_3218_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3217_, 0);
                    leanh::lean_ctor_set(v___x_3217_, 0, v___x_3219_);
                    v___x_3221_ = v___x_3217_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
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
    mut v_g_3224_: *mut leanh::LeanObject,
    mut v_e_3225_: *mut leanh::LeanObject,
    mut v_a_3226_: *mut leanh::LeanObject,
    mut v___y_3227_: *mut leanh::LeanObject,
    mut v___y_3228_: *mut leanh::LeanObject,
    mut v___y_3229_: *mut leanh::LeanObject,
    mut v___y_3230_: *mut leanh::LeanObject,
    mut v___y_3231_: *mut leanh::LeanObject,
    mut v___y_3232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3231_);
    leanh::lean_dec_ref(v___y_3230_);
    leanh::lean_dec(v___y_3229_);
    leanh::lean_dec_ref(v___y_3228_);
    leanh::lean_dec(v_a_3226_);
    return v_res_3233_;
}
pub unsafe fn _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = leanh::lean_box(0);
    v___x_3235_ = leanh::lean_unsigned_to_nat(16);
    v___x_3236_ = lean_mk_array(v___x_3235_, v___x_3234_);
    return v___x_3236_;
}
pub unsafe fn _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3237_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_GoToKind_determineTargetExprs___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Server_GoToKind_determineTargetExprs___closed__0_once),
        _init_l_Lean_Server_GoToKind_determineTargetExprs___closed__0,
    );
    v___x_3238_ = leanh::lean_unsigned_to_nat(0);
    v___x_3239_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3239_, 0, v___x_3238_);
    leanh::lean_ctor_set(v___x_3239_, 1, v___x_3237_);
    return v___x_3239_;
}
pub unsafe fn l_Lean_Server_GoToKind_determineTargetExprs(
    mut v_kind_3243_: u8,
    mut v_ti_3244_: *mut leanh::LeanObject,
    mut v_a_3245_: *mut leanh::LeanObject,
    mut v_a_3246_: *mut leanh::LeanObject,
    mut v_a_3247_: *mut leanh::LeanObject,
    mut v_a_3248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_expr_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3263_: u8 = 0;
    let mut v_snd_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3269_: u8 = 0;
    let mut v_a_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut v_a_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v_expr_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_kind_3243_ == 2 {
                    v_expr_3250_ = leanh::lean_ctor_get(v_ti_3244_, 3);
                    leanh::lean_inc_ref(v_expr_3250_);
                    leanh::lean_dec_ref(v_ti_3244_);
                    leanh::lean_inc(v_a_3248_);
                    leanh::lean_inc_ref(v_a_3247_);
                    leanh::lean_inc(v_a_3246_);
                    leanh::lean_inc_ref(v_a_3245_);
                    v___x_3251_ =
                        lean_infer_type(v_expr_3250_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
                    if leanh::lean_obj_tag(v___x_3251_) == 0 {
                        v_a_3252_ = leanh::lean_ctor_get(v___x_3251_, 0);
                        leanh::lean_inc(v_a_3252_);
                        leanh::lean_dec_ref_known(v___x_3251_, 1);
                        v___x_3253_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_a_3252_, v_a_3246_);
                        v_a_3254_ = leanh::lean_ctor_get(v___x_3253_, 0);
                        leanh::lean_inc(v_a_3254_);
                        leanh::lean_dec_ref(v___x_3253_);
                        v___x_3255_ = leanh::lean_obj_once(
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
                        if leanh::lean_obj_tag(v___x_3259_) == 0 {
                            v_a_3260_ = leanh::lean_ctor_get(v___x_3259_, 0);
                            v_isSharedCheck_3269_ =
                                (!leanh::lean_is_exclusive(v___x_3259_)) as u8;
                            if v_isSharedCheck_3269_ == 0 {
                                v___x_3262_ = v___x_3259_;
                                v_isShared_3263_ = v_isSharedCheck_3269_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3260_);
                                leanh::lean_dec(v___x_3259_);
                                v___x_3262_ = leanh::lean_box(0);
                                v_isShared_3263_ = v_isSharedCheck_3269_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_3256_);
                            v_a_3270_ = leanh::lean_ctor_get(v___x_3259_, 0);
                            v_isSharedCheck_3277_ =
                                (!leanh::lean_is_exclusive(v___x_3259_)) as u8;
                            if v_isSharedCheck_3277_ == 0 {
                                v___x_3272_ = v___x_3259_;
                                v_isShared_3273_ = v_isSharedCheck_3277_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3270_);
                                leanh::lean_dec(v___x_3259_);
                                v___x_3272_ = leanh::lean_box(0);
                                v_isShared_3273_ = v_isSharedCheck_3277_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_3278_ = leanh::lean_ctor_get(v___x_3251_, 0);
                        v_isSharedCheck_3285_ =
                            (!leanh::lean_is_exclusive(v___x_3251_)) as u8;
                        if v_isSharedCheck_3285_ == 0 {
                            v___x_3280_ = v___x_3251_;
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3278_);
                            leanh::lean_dec(v___x_3251_);
                            v___x_3280_ = leanh::lean_box(0);
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_expr_3286_ = leanh::lean_ctor_get(v_ti_3244_, 3);
                    leanh::lean_inc_ref(v_expr_3286_);
                    leanh::lean_dec_ref(v_ti_3244_);
                    v___x_3287_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_3286_, v_a_3246_);
                    v_a_3288_ = leanh::lean_ctor_get(v___x_3287_, 0);
                    v_isSharedCheck_3298_ = (!leanh::lean_is_exclusive(v___x_3287_)) as u8;
                    if v_isSharedCheck_3298_ == 0 {
                        v___x_3290_ = v___x_3287_;
                        v_isShared_3291_ = v_isSharedCheck_3298_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3288_);
                        leanh::lean_dec(v___x_3287_);
                        v___x_3290_ = leanh::lean_box(0);
                        v_isShared_3291_ = v_isSharedCheck_3298_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3264_ = leanh::lean_ctor_get(v_a_3260_, 1);
                leanh::lean_inc(v_snd_3264_);
                leanh::lean_dec(v_a_3260_);
                v___x_3265_ = lean_st_ref_get(v___x_3256_);
                leanh::lean_dec(v___x_3256_);
                leanh::lean_dec(v___x_3265_);
                if v_isShared_3263_ == 0 {
                    leanh::lean_ctor_set(v___x_3262_, 0, v_snd_3264_);
                    v___x_3267_ = v___x_3262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_snd_3264_);
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
                    v_reuseFailAlloc_3276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
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
                    v_reuseFailAlloc_3284_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
                    v___x_3283_ = v_reuseFailAlloc_3284_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3283_;
            }
            7 => {
                v___x_3292_ = leanh::lean_unsigned_to_nat(1);
                v___x_3293_ = lean_mk_empty_array_with_capacity(v___x_3292_);
                v___x_3294_ = lean_array_push(v___x_3293_, v_a_3288_);
                if v_isShared_3291_ == 0 {
                    leanh::lean_ctor_set(v___x_3290_, 0, v___x_3294_);
                    v___x_3296_ = v___x_3290_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3297_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
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
    mut v_kind_3299_: *mut leanh::LeanObject,
    mut v_ti_3300_: *mut leanh::LeanObject,
    mut v_a_3301_: *mut leanh::LeanObject,
    mut v_a_3302_: *mut leanh::LeanObject,
    mut v_a_3303_: *mut leanh::LeanObject,
    mut v_a_3304_: *mut leanh::LeanObject,
    mut v_a_3305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_3306_: u8 = 0;
    let mut v_res_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3306_ = (leanh::lean_unbox(v_kind_3299_) as u8);
    v_res_3307_ = l_Lean_Server_GoToKind_determineTargetExprs(
        v_kind_boxed_3306_,
        v_ti_3300_,
        v_a_3301_,
        v_a_3302_,
        v_a_3303_,
        v_a_3304_,
    );
    leanh::lean_dec(v_a_3304_);
    leanh::lean_dec_ref(v_a_3303_);
    leanh::lean_dec(v_a_3302_);
    leanh::lean_dec_ref(v_a_3301_);
    return v_res_3307_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(
    mut v_00_u03b2_3308_: *mut leanh::LeanObject,
    mut v_m_3309_: *mut leanh::LeanObject,
    mut v_a_3310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___redArg(v_m_3309_, v_a_3310_);
    return v___x_3311_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1___boxed(
    mut v_00_u03b2_3312_: *mut leanh::LeanObject,
    mut v_m_3313_: *mut leanh::LeanObject,
    mut v_a_3314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1(v_00_u03b2_3312_, v_m_3313_, v_a_3314_);
    leanh::lean_dec_ref(v_a_3314_);
    leanh::lean_dec_ref(v_m_3313_);
    return v_res_3315_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2(
    mut v_00_u03b2_3316_: *mut leanh::LeanObject,
    mut v_m_3317_: *mut leanh::LeanObject,
    mut v_a_3318_: *mut leanh::LeanObject,
    mut v_b_3319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2___redArg(v_m_3317_, v_a_3318_, v_b_3319_);
    return v___x_3320_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(
    mut v_00_u03b2_3321_: *mut leanh::LeanObject,
    mut v_a_3322_: *mut leanh::LeanObject,
    mut v_x_3323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___redArg(v_a_3322_, v_x_3323_);
    return v___x_3324_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_3325_: *mut leanh::LeanObject,
    mut v_a_3326_: *mut leanh::LeanObject,
    mut v_x_3327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__1_spec__2(v_00_u03b2_3325_, v_a_3326_, v_x_3327_);
    leanh::lean_dec(v_x_3327_);
    leanh::lean_dec_ref(v_a_3326_);
    return v_res_3328_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3329_: *mut leanh::LeanObject,
    mut v_a_3330_: *mut leanh::LeanObject,
    mut v_x_3331_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3332_: u8 = 0;
    v___x_3332_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___redArg(v_a_3330_, v_x_3331_);
    return v___x_3332_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_x_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3336_: u8 = 0;
    let mut v_r_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__4(v_00_u03b2_3333_, v_a_3334_, v_x_3335_);
    leanh::lean_dec(v_x_3335_);
    leanh::lean_dec_ref(v_a_3334_);
    v_r_3337_ = leanh::lean_box((v_res_3336_) as usize);
    return v_r_3337_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5(
    mut v_00_u03b2_3338_: *mut leanh::LeanObject,
    mut v_data_3339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3340_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5___redArg(v_data_3339_);
    return v___x_3340_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6(
    mut v_00_u03b2_3341_: *mut leanh::LeanObject,
    mut v_a_3342_: *mut leanh::LeanObject,
    mut v_b_3343_: *mut leanh::LeanObject,
    mut v_x_3344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__6___redArg(v_a_3342_, v_b_3343_, v_x_3344_);
    return v___x_3345_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6(
    mut v_00_u03b2_3346_: *mut leanh::LeanObject,
    mut v_i_3347_: *mut leanh::LeanObject,
    mut v_source_3348_: *mut leanh::LeanObject,
    mut v_target_3349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3350_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6___redArg(v_i_3347_, v_source_3348_, v_target_3349_);
    return v___x_3350_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7(
    mut v_00_u03b2_3351_: *mut leanh::LeanObject,
    mut v_x_3352_: *mut leanh::LeanObject,
    mut v_x_3353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Server_GoToKind_determineTargetExprs_spec__1_spec__2_spec__5_spec__6_spec__7___redArg(v_x_3352_, v_x_3353_);
    return v___x_3354_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(
    mut v_e_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
    mut v_a_3357_: *mut leanh::LeanObject,
    mut v_a_3358_: *mut leanh::LeanObject,
    mut v_a_3359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut v___x_3376_: u8 = 0;
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3381_: u8 = 0;
    let mut v_val_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3388_: u8 = 0;
    let mut v_a_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3392_: u8 = 0;
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3361_ = lean_st_ref_get(v_a_3359_);
                v___x_3362_ = l_Lean_Expr_getAppFn_x27(v_e_3355_);
                if leanh::lean_obj_tag(v___x_3362_) == 4 {
                    v_declName_3363_ = leanh::lean_ctor_get(v___x_3362_, 0);
                    leanh::lean_inc(v_declName_3363_);
                    leanh::lean_dec_ref_known(v___x_3362_, 2);
                    v_env_3364_ = leanh::lean_ctor_get(v___x_3361_, 0);
                    leanh::lean_inc_ref(v_env_3364_);
                    leanh::lean_dec(v___x_3361_);
                    v___x_3365_ =
                        l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3364_, v_declName_3363_);
                    if leanh::lean_obj_tag(v___x_3365_) == 1 {
                        v_val_3366_ = leanh::lean_ctor_get(v___x_3365_, 0);
                        v_isSharedCheck_3375_ =
                            (!leanh::lean_is_exclusive(v___x_3365_)) as u8;
                        if v_isSharedCheck_3375_ == 0 {
                            v___x_3368_ = v___x_3365_;
                            v_isShared_3369_ = v_isSharedCheck_3375_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3366_);
                            leanh::lean_dec(v___x_3365_);
                            v___x_3368_ = leanh::lean_box(0);
                            v_isShared_3369_ = v_isSharedCheck_3375_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3365_);
                        v___x_3376_ = 0;
                        v___x_3377_ = l_Lean_Meta_unfoldDefinition_x3f(
                            v_e_3355_,
                            v___x_3376_,
                            v_a_3356_,
                            v_a_3357_,
                            v_a_3358_,
                            v_a_3359_,
                        );
                        if leanh::lean_obj_tag(v___x_3377_) == 0 {
                            v_a_3378_ = leanh::lean_ctor_get(v___x_3377_, 0);
                            v_isSharedCheck_3388_ =
                                (!leanh::lean_is_exclusive(v___x_3377_)) as u8;
                            if v_isSharedCheck_3388_ == 0 {
                                v___x_3380_ = v___x_3377_;
                                v_isShared_3381_ = v_isSharedCheck_3388_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3378_);
                                leanh::lean_dec(v___x_3377_);
                                v___x_3380_ = leanh::lean_box(0);
                                v_isShared_3381_ = v_isSharedCheck_3388_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_3389_ = leanh::lean_ctor_get(v___x_3377_, 0);
                            v_isSharedCheck_3396_ =
                                (!leanh::lean_is_exclusive(v___x_3377_)) as u8;
                            if v_isSharedCheck_3396_ == 0 {
                                v___x_3391_ = v___x_3377_;
                                v_isShared_3392_ = v_isSharedCheck_3396_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3389_);
                                leanh::lean_dec(v___x_3377_);
                                v___x_3391_ = leanh::lean_box(0);
                                v_isShared_3392_ = v_isSharedCheck_3396_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3362_);
                    leanh::lean_dec(v___x_3361_);
                    leanh::lean_dec_ref(v_e_3355_);
                    v___x_3397_ = leanh::lean_box(0);
                    v___x_3398_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3398_, 0, v___x_3397_);
                    return v___x_3398_;
                }
            }
            1 => {
                v___x_3370_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3370_, 0, v_e_3355_);
                leanh::lean_ctor_set(v___x_3370_, 1, v_val_3366_);
                if v_isShared_3369_ == 0 {
                    leanh::lean_ctor_set(v___x_3368_, 0, v___x_3370_);
                    v___x_3372_ = v___x_3368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3374_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3370_);
                    v___x_3372_ = v_reuseFailAlloc_3374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3373_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3373_, 0, v___x_3372_);
                return v___x_3373_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3378_) == 1 {
                    leanh::lean_del_object(v___x_3380_);
                    v_val_3382_ = leanh::lean_ctor_get(v_a_3378_, 0);
                    leanh::lean_inc(v_val_3382_);
                    leanh::lean_dec_ref_known(v_a_3378_, 1);
                    v_e_3355_ = v_val_3382_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_3378_);
                    v___x_3384_ = leanh::lean_box(0);
                    if v_isShared_3381_ == 0 {
                        leanh::lean_ctor_set(v___x_3380_, 0, v___x_3384_);
                        v___x_3386_ = v___x_3380_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3387_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
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
                    v_reuseFailAlloc_3395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
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
    mut v_e_3399_: *mut leanh::LeanObject,
    mut v_a_3400_: *mut leanh::LeanObject,
    mut v_a_3401_: *mut leanh::LeanObject,
    mut v_a_3402_: *mut leanh::LeanObject,
    mut v_a_3403_: *mut leanh::LeanObject,
    mut v_a_3404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3405_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
    leanh::lean_dec(v_a_3403_);
    leanh::lean_dec_ref(v_a_3402_);
    leanh::lean_dec(v_a_3401_);
    leanh::lean_dec_ref(v_a_3400_);
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
-> *mut leanh::LeanObject {
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3408_ = leanh::lean_box(0);
    v_dummy_3409_ = l_Lean_Expr_sort___override(v___x_3408_);
    return v_dummy_3409_;
}
pub unsafe fn l_Lean_Server_getInstanceProjectionArg_x3f(
    mut v_e_3410_: *mut leanh::LeanObject,
    mut v_a_3411_: *mut leanh::LeanObject,
    mut v_a_3412_: *mut leanh::LeanObject,
    mut v_a_3413_: *mut leanh::LeanObject,
    mut v_a_3414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3437_: u8 = 0;
    let mut v_trackZetaDelta_3438_: u8 = 0;
    let mut v_zetaDeltaSet_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3445_: u8 = 0;
    let mut v_inTypeClassResolution_3446_: u8 = 0;
    let mut v_cacheInferType_3447_: u8 = 0;
    let mut v___x_3448_: u8 = 0;
    let mut v_config_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: u64 = 0;
    let mut v___x_3452_: u64 = 0;
    let mut v___x_3453_: u64 = 0;
    let mut v___x_3454_: u64 = 0;
    let mut v___x_3455_: u64 = 0;
    let mut v_key_3456_: u64 = 0;
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3463_: u8 = 0;
    let mut v_val_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v_snd_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3490_: u8 = 0;
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut v_a_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3499_: u8 = 0;
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3503_: u8 = 0;
    let mut v_reuseFailAlloc_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3416_ = l_Lean_Meta_Context_config(v_a_3411_);
                v_foApprox_3417_ = leanh::lean_ctor_get_uint8(v___x_3416_, 0 as u32);
                v_ctxApprox_3418_ = leanh::lean_ctor_get_uint8(v___x_3416_, 1 as u32);
                v_quasiPatternApprox_3419_ =
                    leanh::lean_ctor_get_uint8(v___x_3416_, 2 as u32);
                v_constApprox_3420_ = leanh::lean_ctor_get_uint8(v___x_3416_, 3 as u32);
                v_isDefEqStuckEx_3421_ = leanh::lean_ctor_get_uint8(v___x_3416_, 4 as u32);
                v_unificationHints_3422_ = leanh::lean_ctor_get_uint8(v___x_3416_, 5 as u32);
                v_proofIrrelevance_3423_ = leanh::lean_ctor_get_uint8(v___x_3416_, 6 as u32);
                v_assignSyntheticOpaque_3424_ =
                    leanh::lean_ctor_get_uint8(v___x_3416_, 7 as u32);
                v_offsetCnstrs_3425_ = leanh::lean_ctor_get_uint8(v___x_3416_, 8 as u32);
                v_etaStruct_3426_ = leanh::lean_ctor_get_uint8(v___x_3416_, 10 as u32);
                v_univApprox_3427_ = leanh::lean_ctor_get_uint8(v___x_3416_, 11 as u32);
                v_iota_3428_ = leanh::lean_ctor_get_uint8(v___x_3416_, 12 as u32);
                v_beta_3429_ = leanh::lean_ctor_get_uint8(v___x_3416_, 13 as u32);
                v_proj_3430_ = leanh::lean_ctor_get_uint8(v___x_3416_, 14 as u32);
                v_zeta_3431_ = leanh::lean_ctor_get_uint8(v___x_3416_, 15 as u32);
                v_zetaDelta_3432_ = leanh::lean_ctor_get_uint8(v___x_3416_, 16 as u32);
                v_zetaUnused_3433_ = leanh::lean_ctor_get_uint8(v___x_3416_, 17 as u32);
                v_zetaHave_3434_ = leanh::lean_ctor_get_uint8(v___x_3416_, 18 as u32);
                v_isSharedCheck_3505_ = (!leanh::lean_is_exclusive(v___x_3416_)) as u8;
                if v_isSharedCheck_3505_ == 0 {
                    v___x_3436_ = v___x_3416_;
                    v_isShared_3437_ = v_isSharedCheck_3505_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3416_);
                    v___x_3436_ = leanh::lean_box(0);
                    v_isShared_3437_ = v_isSharedCheck_3505_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_3438_ = leanh::lean_ctor_get_uint8(
                    v_a_3411_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3439_ = leanh::lean_ctor_get(v_a_3411_, 1);
                v_lctx_3440_ = leanh::lean_ctor_get(v_a_3411_, 2);
                v_localInstances_3441_ = leanh::lean_ctor_get(v_a_3411_, 3);
                v_defEqCtx_x3f_3442_ = leanh::lean_ctor_get(v_a_3411_, 4);
                v_synthPendingDepth_3443_ = leanh::lean_ctor_get(v_a_3411_, 5);
                v_canUnfold_x3f_3444_ = leanh::lean_ctor_get(v_a_3411_, 6);
                v_univApprox_3445_ = leanh::lean_ctor_get_uint8(
                    v_a_3411_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3446_ = leanh::lean_ctor_get_uint8(
                    v_a_3411_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3447_ = leanh::lean_ctor_get_uint8(
                    v_a_3411_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3448_ = 2;
                if v_isShared_3437_ == 0 {
                    v_config_3450_ = v___x_3436_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3504_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        0 as u32,
                        v_foApprox_3417_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        1 as u32,
                        v_ctxApprox_3418_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        2 as u32,
                        v_quasiPatternApprox_3419_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        3 as u32,
                        v_constApprox_3420_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        4 as u32,
                        v_isDefEqStuckEx_3421_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        5 as u32,
                        v_unificationHints_3422_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        6 as u32,
                        v_proofIrrelevance_3423_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        7 as u32,
                        v_assignSyntheticOpaque_3424_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        8 as u32,
                        v_offsetCnstrs_3425_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        10 as u32,
                        v_etaStruct_3426_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        11 as u32,
                        v_univApprox_3427_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        12 as u32,
                        v_iota_3428_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        13 as u32,
                        v_beta_3429_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        14 as u32,
                        v_proj_3430_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        15 as u32,
                        v_zeta_3431_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        16 as u32,
                        v_zetaDelta_3432_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3504_,
                        17 as u32,
                        v_zetaUnused_3433_,
                    );
                    leanh::lean_ctor_set_uint8(
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
                leanh::lean_ctor_set_uint8(v_config_3450_, 9 as u32, v___x_3448_);
                v___x_3451_ = l_Lean_Meta_Context_configKey(v_a_3411_);
                v___x_3452_ = 3u64;
                v___x_3453_ = lean_uint64_shift_right(v___x_3451_, v___x_3452_);
                v___x_3454_ = lean_uint64_shift_left(v___x_3453_, v___x_3452_);
                v___x_3455_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_getInstanceProjectionArg_x3f___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_getInstanceProjectionArg_x3f___closed__0_once
                    ),
                    _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__0,
                );
                v_key_3456_ = lean_uint64_lor(v___x_3454_, v___x_3455_);
                v___x_3457_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_3457_, 0, v_config_3450_);
                leanh::lean_ctor_set_uint64(
                    v___x_3457_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_3456_,
                );
                leanh::lean_inc(v_canUnfold_x3f_3444_);
                leanh::lean_inc(v_synthPendingDepth_3443_);
                leanh::lean_inc(v_defEqCtx_x3f_3442_);
                leanh::lean_inc_ref(v_localInstances_3441_);
                leanh::lean_inc_ref(v_lctx_3440_);
                leanh::lean_inc(v_zetaDeltaSet_3439_);
                v___x_3458_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_3458_, 0, v___x_3457_);
                leanh::lean_ctor_set(v___x_3458_, 1, v_zetaDeltaSet_3439_);
                leanh::lean_ctor_set(v___x_3458_, 2, v_lctx_3440_);
                leanh::lean_ctor_set(v___x_3458_, 3, v_localInstances_3441_);
                leanh::lean_ctor_set(v___x_3458_, 4, v_defEqCtx_x3f_3442_);
                leanh::lean_ctor_set(v___x_3458_, 5, v_synthPendingDepth_3443_);
                leanh::lean_ctor_set(v___x_3458_, 6, v_canUnfold_x3f_3444_);
                leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3438_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3445_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3446_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3447_,
                );
                v___x_3459_ = l___private_Lean_Server_GoTo_0__Lean_Server_getInstanceProjectionArg_x3f_reduceToProjection_x3f(v_e_3410_, v___x_3458_, v_a_3412_, v_a_3413_, v_a_3414_);
                leanh::lean_dec_ref_known(v___x_3458_, 7);
                if leanh::lean_obj_tag(v___x_3459_) == 0 {
                    v_a_3460_ = leanh::lean_ctor_get(v___x_3459_, 0);
                    v_isSharedCheck_3495_ = (!leanh::lean_is_exclusive(v___x_3459_)) as u8;
                    if v_isSharedCheck_3495_ == 0 {
                        v___x_3462_ = v___x_3459_;
                        v_isShared_3463_ = v_isSharedCheck_3495_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3460_);
                        leanh::lean_dec(v___x_3459_);
                        v___x_3462_ = leanh::lean_box(0);
                        v_isShared_3463_ = v_isSharedCheck_3495_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_3496_ = leanh::lean_ctor_get(v___x_3459_, 0);
                    v_isSharedCheck_3503_ = (!leanh::lean_is_exclusive(v___x_3459_)) as u8;
                    if v_isSharedCheck_3503_ == 0 {
                        v___x_3498_ = v___x_3459_;
                        v_isShared_3499_ = v_isSharedCheck_3503_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3496_);
                        leanh::lean_dec(v___x_3459_);
                        v___x_3498_ = leanh::lean_box(0);
                        v_isShared_3499_ = v_isSharedCheck_3503_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3460_) == 1 {
                    v_val_3464_ = leanh::lean_ctor_get(v_a_3460_, 0);
                    v_isSharedCheck_3490_ = (!leanh::lean_is_exclusive(v_a_3460_)) as u8;
                    if v_isSharedCheck_3490_ == 0 {
                        v___x_3466_ = v_a_3460_;
                        v_isShared_3467_ = v_isSharedCheck_3490_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3464_);
                        leanh::lean_dec(v_a_3460_);
                        v___x_3466_ = leanh::lean_box(0);
                        v_isShared_3467_ = v_isSharedCheck_3490_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3460_);
                    v___x_3491_ = leanh::lean_box(0);
                    if v_isShared_3463_ == 0 {
                        leanh::lean_ctor_set(v___x_3462_, 0, v___x_3491_);
                        v___x_3493_ = v___x_3462_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3494_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
                        v___x_3493_ = v_reuseFailAlloc_3494_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_snd_3468_ = leanh::lean_ctor_get(v_val_3464_, 1);
                leanh::lean_inc(v_snd_3468_);
                v_fst_3469_ = leanh::lean_ctor_get(v_val_3464_, 0);
                leanh::lean_inc(v_fst_3469_);
                leanh::lean_dec(v_val_3464_);
                v_numParams_3470_ = leanh::lean_ctor_get(v_snd_3468_, 1);
                leanh::lean_inc(v_numParams_3470_);
                leanh::lean_dec(v_snd_3468_);
                v_dummy_3471_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_getInstanceProjectionArg_x3f___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_getInstanceProjectionArg_x3f___closed__1_once
                    ),
                    _init_l_Lean_Server_getInstanceProjectionArg_x3f___closed__1,
                );
                v_nargs_3472_ = l_Lean_Expr_getAppNumArgs(v_fst_3469_);
                leanh::lean_inc(v_nargs_3472_);
                v___x_3473_ = lean_mk_array(v_nargs_3472_, v_dummy_3471_);
                v___x_3474_ = leanh::lean_unsigned_to_nat(1);
                v___x_3475_ = lean_nat_sub(v_nargs_3472_, v___x_3474_);
                leanh::lean_dec(v_nargs_3472_);
                v___x_3476_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_fst_3469_,
                    v___x_3473_,
                    v___x_3475_,
                );
                v___x_3477_ = lean_array_get_size(v___x_3476_);
                v___x_3478_ = lean_nat_dec_lt(v_numParams_3470_, v___x_3477_);
                if v___x_3478_ == 0 {
                    leanh::lean_dec_ref(v___x_3476_);
                    leanh::lean_dec(v_numParams_3470_);
                    leanh::lean_del_object(v___x_3466_);
                    v___x_3479_ = leanh::lean_box(0);
                    if v_isShared_3463_ == 0 {
                        leanh::lean_ctor_set(v___x_3462_, 0, v___x_3479_);
                        v___x_3481_ = v___x_3462_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3482_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
                        v___x_3481_ = v_reuseFailAlloc_3482_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_3483_ = lean_array_fget(v___x_3476_, v_numParams_3470_);
                    leanh::lean_dec(v_numParams_3470_);
                    leanh::lean_dec_ref(v___x_3476_);
                    if v_isShared_3467_ == 0 {
                        leanh::lean_ctor_set(v___x_3466_, 0, v___x_3483_);
                        v___x_3485_ = v___x_3466_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3489_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3483_);
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
                    leanh::lean_ctor_set(v___x_3462_, 0, v___x_3485_);
                    v___x_3487_ = v___x_3462_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
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
                    v_reuseFailAlloc_3502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
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
    mut v_e_3506_: *mut leanh::LeanObject,
    mut v_a_3507_: *mut leanh::LeanObject,
    mut v_a_3508_: *mut leanh::LeanObject,
    mut v_a_3509_: *mut leanh::LeanObject,
    mut v_a_3510_: *mut leanh::LeanObject,
    mut v_a_3511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Lean_Server_getInstanceProjectionArg_x3f(
        v_e_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_,
    );
    leanh::lean_dec(v_a_3510_);
    leanh::lean_dec_ref(v_a_3509_);
    leanh::lean_dec(v_a_3508_);
    leanh::lean_dec_ref(v_a_3507_);
    return v_res_3512_;
}
pub unsafe fn l_Lean_Server_isInstanceProjection(
    mut v_e_3513_: *mut leanh::LeanObject,
    mut v_a_3514_: *mut leanh::LeanObject,
    mut v_a_3515_: *mut leanh::LeanObject,
    mut v_a_3516_: *mut leanh::LeanObject,
    mut v_a_3517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3524_: u8 = 0;
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut v_a_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3519_ = l_Lean_Server_getInstanceProjectionArg_x3f(
                    v_e_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_,
                );
                if leanh::lean_obj_tag(v___x_3519_) == 0 {
                    v_a_3520_ = leanh::lean_ctor_get(v___x_3519_, 0);
                    v_isSharedCheck_3534_ = (!leanh::lean_is_exclusive(v___x_3519_)) as u8;
                    if v_isSharedCheck_3534_ == 0 {
                        v___x_3522_ = v___x_3519_;
                        v_isShared_3523_ = v_isSharedCheck_3534_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3520_);
                        leanh::lean_dec(v___x_3519_);
                        v___x_3522_ = leanh::lean_box(0);
                        v_isShared_3523_ = v_isSharedCheck_3534_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3535_ = leanh::lean_ctor_get(v___x_3519_, 0);
                    v_isSharedCheck_3542_ = (!leanh::lean_is_exclusive(v___x_3519_)) as u8;
                    if v_isSharedCheck_3542_ == 0 {
                        v___x_3537_ = v___x_3519_;
                        v_isShared_3538_ = v_isSharedCheck_3542_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3535_);
                        leanh::lean_dec(v___x_3519_);
                        v___x_3537_ = leanh::lean_box(0);
                        v_isShared_3538_ = v_isSharedCheck_3542_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3520_) == 0 {
                    v___x_3524_ = 0;
                    v___x_3525_ = leanh::lean_box((v___x_3524_) as usize);
                    if v_isShared_3523_ == 0 {
                        leanh::lean_ctor_set(v___x_3522_, 0, v___x_3525_);
                        v___x_3527_ = v___x_3522_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3528_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
                        v___x_3527_ = v_reuseFailAlloc_3528_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_3520_, 1);
                    v___x_3529_ = 1;
                    v___x_3530_ = leanh::lean_box((v___x_3529_) as usize);
                    if v_isShared_3523_ == 0 {
                        leanh::lean_ctor_set(v___x_3522_, 0, v___x_3530_);
                        v___x_3532_ = v___x_3522_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3533_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
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
                    v_reuseFailAlloc_3541_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
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
    mut v_e_3543_: *mut leanh::LeanObject,
    mut v_a_3544_: *mut leanh::LeanObject,
    mut v_a_3545_: *mut leanh::LeanObject,
    mut v_a_3546_: *mut leanh::LeanObject,
    mut v_a_3547_: *mut leanh::LeanObject,
    mut v_a_3548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3549_ =
        l_Lean_Server_isInstanceProjection(v_e_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_);
    leanh::lean_dec(v_a_3547_);
    leanh::lean_dec_ref(v_a_3546_);
    leanh::lean_dec(v_a_3545_);
    leanh::lean_dec_ref(v_a_3544_);
    return v_res_3549_;
}
pub unsafe fn l_Lean_Server_isInstanceProjectionInfoFor(
    mut v_kind_3550_: u8,
    mut v_ti1_3551_: *mut leanh::LeanObject,
    mut v_ti2_3552_: *mut leanh::LeanObject,
    mut v_a_3553_: *mut leanh::LeanObject,
    mut v_a_3554_: *mut leanh::LeanObject,
    mut v_a_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: u8 = 0;
    let mut v_toElabInfo_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: u8 = 0;
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v_expr_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3592_: u8 = 0;
    let mut v___y_3594_: u8 = 0;
    let mut v___x_3595_: u8 = 0;
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v_isSharedCheck_3612_: u8 = 0;
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3617_: u8 = 0;
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3558_ = 2;
                v___x_3559_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_3550_, v___x_3558_);
                if v___x_3559_ == 0 {
                    v_toElabInfo_3560_ = leanh::lean_ctor_get(v_ti1_3551_, 0);
                    leanh::lean_inc_ref(v_toElabInfo_3560_);
                    v_expr_3561_ = leanh::lean_ctor_get(v_ti1_3551_, 3);
                    leanh::lean_inc_ref(v_expr_3561_);
                    leanh::lean_dec_ref(v_ti1_3551_);
                    v_stx_3562_ = leanh::lean_ctor_get(v_toElabInfo_3560_, 1);
                    leanh::lean_inc(v_stx_3562_);
                    leanh::lean_dec_ref(v_toElabInfo_3560_);
                    v___x_3563_ = 1;
                    v___x_3564_ = l_Lean_Syntax_getPos_x3f(v_stx_3562_, v___x_3563_);
                    leanh::lean_dec(v_stx_3562_);
                    if leanh::lean_obj_tag(v___x_3564_) == 1 {
                        v_toElabInfo_3565_ = leanh::lean_ctor_get(v_ti2_3552_, 0);
                        leanh::lean_inc_ref(v_toElabInfo_3565_);
                        v_val_3566_ = leanh::lean_ctor_get(v___x_3564_, 0);
                        v_isSharedCheck_3622_ =
                            (!leanh::lean_is_exclusive(v___x_3564_)) as u8;
                        if v_isSharedCheck_3622_ == 0 {
                            v___x_3568_ = v___x_3564_;
                            v_isShared_3569_ = v_isSharedCheck_3622_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3566_);
                            leanh::lean_dec(v___x_3564_);
                            v___x_3568_ = leanh::lean_box(0);
                            v_isShared_3569_ = v_isSharedCheck_3622_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3564_);
                        leanh::lean_dec_ref(v_expr_3561_);
                        leanh::lean_dec_ref(v_ti2_3552_);
                        v___x_3623_ = leanh::lean_box((v___x_3559_) as usize);
                        v___x_3624_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3624_, 0, v___x_3623_);
                        return v___x_3624_;
                    }
                } else {
                    leanh::lean_dec_ref(v_ti2_3552_);
                    leanh::lean_dec_ref(v_ti1_3551_);
                    v___x_3625_ = 0;
                    v___x_3626_ = leanh::lean_box((v___x_3625_) as usize);
                    v___x_3627_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3627_, 0, v___x_3626_);
                    return v___x_3627_;
                }
            }
            1 => {
                v_expr_3570_ = leanh::lean_ctor_get(v_ti2_3552_, 3);
                leanh::lean_inc_ref(v_expr_3570_);
                leanh::lean_dec_ref(v_ti2_3552_);
                v_stx_3571_ = leanh::lean_ctor_get(v_toElabInfo_3565_, 1);
                leanh::lean_inc(v_stx_3571_);
                leanh::lean_dec_ref(v_toElabInfo_3565_);
                v___x_3572_ = l_Lean_Syntax_getPos_x3f(v_stx_3571_, v___x_3563_);
                leanh::lean_dec(v_stx_3571_);
                if leanh::lean_obj_tag(v___x_3572_) == 1 {
                    leanh::lean_del_object(v___x_3568_);
                    v_val_3573_ = leanh::lean_ctor_get(v___x_3572_, 0);
                    v_isSharedCheck_3617_ = (!leanh::lean_is_exclusive(v___x_3572_)) as u8;
                    if v_isSharedCheck_3617_ == 0 {
                        v___x_3575_ = v___x_3572_;
                        v_isShared_3576_ = v_isSharedCheck_3617_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3573_);
                        leanh::lean_dec(v___x_3572_);
                        v___x_3575_ = leanh::lean_box(0);
                        v_isShared_3576_ = v_isSharedCheck_3617_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3572_);
                    leanh::lean_dec_ref(v_expr_3570_);
                    leanh::lean_dec(v_val_3566_);
                    leanh::lean_dec_ref(v_expr_3561_);
                    v___x_3618_ = leanh::lean_box((v___x_3559_) as usize);
                    if v_isShared_3569_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3568_, 0);
                        leanh::lean_ctor_set(v___x_3568_, 0, v___x_3618_);
                        v___x_3620_ = v___x_3568_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3621_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
                        v___x_3620_ = v_reuseFailAlloc_3621_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3577_ = lean_nat_dec_eq(v_val_3566_, v_val_3573_);
                leanh::lean_dec(v_val_3573_);
                leanh::lean_dec(v_val_3566_);
                if v___x_3577_ == 0 {
                    leanh::lean_dec_ref(v_expr_3570_);
                    leanh::lean_dec_ref(v_expr_3561_);
                    v___x_3578_ = leanh::lean_box((v___x_3559_) as usize);
                    if v_isShared_3576_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3575_, 0);
                        leanh::lean_ctor_set(v___x_3575_, 0, v___x_3578_);
                        v___x_3580_ = v___x_3575_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3581_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
                        v___x_3580_ = v_reuseFailAlloc_3581_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v___x_3559_ == 0 {
                        leanh::lean_del_object(v___x_3575_);
                        v___x_3582_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_3561_, v_a_3554_);
                        v_a_3583_ = leanh::lean_ctor_get(v___x_3582_, 0);
                        leanh::lean_inc_n(v_a_3583_, 2);
                        leanh::lean_dec_ref(v___x_3582_);
                        v___x_3584_ = l_Lean_instantiateMVars___at___00Lean_Server_GoToKind_determineTargetExprs_spec__0___redArg(v_expr_3570_, v_a_3554_);
                        v_a_3585_ = leanh::lean_ctor_get(v___x_3584_, 0);
                        leanh::lean_inc(v_a_3585_);
                        leanh::lean_dec_ref(v___x_3584_);
                        v___x_3586_ = l_Lean_Server_isInstanceProjection(
                            v_a_3583_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                        );
                        if leanh::lean_obj_tag(v___x_3586_) == 0 {
                            v_a_3587_ = leanh::lean_ctor_get(v___x_3586_, 0);
                            leanh::lean_inc(v_a_3587_);
                            leanh::lean_dec_ref_known(v___x_3586_, 1);
                            leanh::lean_inc(v_a_3585_);
                            v___x_3588_ = l_Lean_Server_isInstanceProjection(
                                v_a_3585_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                            );
                            if leanh::lean_obj_tag(v___x_3588_) == 0 {
                                v_a_3589_ = leanh::lean_ctor_get(v___x_3588_, 0);
                                v_isSharedCheck_3612_ =
                                    (!leanh::lean_is_exclusive(v___x_3588_)) as u8;
                                if v_isSharedCheck_3612_ == 0 {
                                    v___x_3591_ = v___x_3588_;
                                    v_isShared_3592_ = v_isSharedCheck_3612_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3589_);
                                    leanh::lean_dec(v___x_3588_);
                                    v___x_3591_ = leanh::lean_box(0);
                                    v_isShared_3592_ = v_isSharedCheck_3612_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_3587_);
                                leanh::lean_dec(v_a_3585_);
                                leanh::lean_dec(v_a_3583_);
                                return v___x_3588_;
                            }
                        } else {
                            leanh::lean_dec(v_a_3585_);
                            leanh::lean_dec(v_a_3583_);
                            return v___x_3586_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_expr_3570_);
                        leanh::lean_dec_ref(v_expr_3561_);
                        v___x_3613_ = leanh::lean_box((v___x_3559_) as usize);
                        if v_isShared_3576_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3575_, 0);
                            leanh::lean_ctor_set(v___x_3575_, 0, v___x_3613_);
                            v___x_3615_ = v___x_3575_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3616_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
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
                v___x_3611_ = (leanh::lean_unbox(v_a_3587_) as u8);
                leanh::lean_dec(v_a_3587_);
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
                    v___x_3595_ = (leanh::lean_unbox(v_a_3589_) as u8);
                    leanh::lean_dec(v_a_3589_);
                    if v___x_3595_ == 0 {
                        v___x_3596_ = l_Lean_Expr_getAppFn_x27(v_a_3583_);
                        leanh::lean_dec(v_a_3583_);
                        v___x_3597_ = l_Lean_Expr_getAppFn_x27(v_a_3585_);
                        leanh::lean_dec(v_a_3585_);
                        v___x_3598_ = lean_expr_eqv(v___x_3596_, v___x_3597_);
                        leanh::lean_dec_ref(v___x_3597_);
                        leanh::lean_dec_ref(v___x_3596_);
                        v___x_3599_ = leanh::lean_box((v___x_3598_) as usize);
                        if v_isShared_3592_ == 0 {
                            leanh::lean_ctor_set(v___x_3591_, 0, v___x_3599_);
                            v___x_3601_ = v___x_3591_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3602_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3599_);
                            v___x_3601_ = v_reuseFailAlloc_3602_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3585_);
                        leanh::lean_dec(v_a_3583_);
                        v___x_3603_ = leanh::lean_box((v___x_3559_) as usize);
                        if v_isShared_3592_ == 0 {
                            leanh::lean_ctor_set(v___x_3591_, 0, v___x_3603_);
                            v___x_3605_ = v___x_3591_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3606_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
                            v___x_3605_ = v_reuseFailAlloc_3606_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3589_);
                    leanh::lean_dec(v_a_3585_);
                    leanh::lean_dec(v_a_3583_);
                    v___x_3607_ = leanh::lean_box((v___x_3559_) as usize);
                    if v_isShared_3592_ == 0 {
                        leanh::lean_ctor_set(v___x_3591_, 0, v___x_3607_);
                        v___x_3609_ = v___x_3591_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3610_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
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
    mut v_kind_3628_: *mut leanh::LeanObject,
    mut v_ti1_3629_: *mut leanh::LeanObject,
    mut v_ti2_3630_: *mut leanh::LeanObject,
    mut v_a_3631_: *mut leanh::LeanObject,
    mut v_a_3632_: *mut leanh::LeanObject,
    mut v_a_3633_: *mut leanh::LeanObject,
    mut v_a_3634_: *mut leanh::LeanObject,
    mut v_a_3635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_3636_: u8 = 0;
    let mut v_res_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3636_ = (leanh::lean_unbox(v_kind_3628_) as u8);
    v_res_3637_ = l_Lean_Server_isInstanceProjectionInfoFor(
        v_kind_boxed_3636_,
        v_ti1_3629_,
        v_ti2_3630_,
        v_a_3631_,
        v_a_3632_,
        v_a_3633_,
        v_a_3634_,
    );
    leanh::lean_dec(v_a_3634_);
    leanh::lean_dec_ref(v_a_3633_);
    leanh::lean_dec(v_a_3632_);
    leanh::lean_dec_ref(v_a_3631_);
    return v_res_3637_;
}
pub unsafe fn l_Lean_Server_GoToM_run___redArg(
    mut v_ctx_3638_: *mut leanh::LeanObject,
    mut v_ci_3639_: *mut leanh::LeanObject,
    mut v_lctx_3640_: *mut leanh::LeanObject,
    mut v_act_3641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3643_ = leanh::lean_apply_1(v_act_3641_, v_ctx_3638_);
    v___x_3644_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_3639_, v_lctx_3640_, v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_Lean_Server_GoToM_run___redArg___boxed(
    mut v_ctx_3645_: *mut leanh::LeanObject,
    mut v_ci_3646_: *mut leanh::LeanObject,
    mut v_lctx_3647_: *mut leanh::LeanObject,
    mut v_act_3648_: *mut leanh::LeanObject,
    mut v_a_3649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ =
        l_Lean_Server_GoToM_run___redArg(v_ctx_3645_, v_ci_3646_, v_lctx_3647_, v_act_3648_);
    return v_res_3650_;
}
pub unsafe fn l_Lean_Server_GoToM_run(
    mut v_00_u03b1_3651_: *mut leanh::LeanObject,
    mut v_ctx_3652_: *mut leanh::LeanObject,
    mut v_ci_3653_: *mut leanh::LeanObject,
    mut v_lctx_3654_: *mut leanh::LeanObject,
    mut v_act_3655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3657_ =
        l_Lean_Server_GoToM_run___redArg(v_ctx_3652_, v_ci_3653_, v_lctx_3654_, v_act_3655_);
    return v___x_3657_;
}
pub unsafe fn l_Lean_Server_GoToM_run___boxed(
    mut v_00_u03b1_3658_: *mut leanh::LeanObject,
    mut v_ctx_3659_: *mut leanh::LeanObject,
    mut v_ci_3660_: *mut leanh::LeanObject,
    mut v_lctx_3661_: *mut leanh::LeanObject,
    mut v_act_3662_: *mut leanh::LeanObject,
    mut v_a_3663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_msgData_3665_: *mut leanh::LeanObject,
    mut v___y_3666_: *mut leanh::LeanObject,
    mut v___y_3667_: *mut leanh::LeanObject,
    mut v___y_3668_: *mut leanh::LeanObject,
    mut v___y_3669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3671_ = lean_st_ref_get(v___y_3669_);
    v_env_3672_ = leanh::lean_ctor_get(v___x_3671_, 0);
    leanh::lean_inc_ref(v_env_3672_);
    leanh::lean_dec(v___x_3671_);
    v___x_3673_ = lean_st_ref_get(v___y_3667_);
    v_mctx_3674_ = leanh::lean_ctor_get(v___x_3673_, 0);
    leanh::lean_inc_ref(v_mctx_3674_);
    leanh::lean_dec(v___x_3673_);
    v_lctx_3675_ = leanh::lean_ctor_get(v___y_3666_, 2);
    v_options_3676_ = leanh::lean_ctor_get(v___y_3668_, 2);
    leanh::lean_inc_ref(v_options_3676_);
    leanh::lean_inc_ref(v_lctx_3675_);
    v___x_3677_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3677_, 0, v_env_3672_);
    leanh::lean_ctor_set(v___x_3677_, 1, v_mctx_3674_);
    leanh::lean_ctor_set(v___x_3677_, 2, v_lctx_3675_);
    leanh::lean_ctor_set(v___x_3677_, 3, v_options_3676_);
    v___x_3678_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3678_, 0, v___x_3677_);
    leanh::lean_ctor_set(v___x_3678_, 1, v_msgData_3665_);
    v___x_3679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3679_, 0, v___x_3678_);
    return v___x_3679_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(
    mut v_msgData_3680_: *mut leanh::LeanObject,
    mut v___y_3681_: *mut leanh::LeanObject,
    mut v___y_3682_: *mut leanh::LeanObject,
    mut v___y_3683_: *mut leanh::LeanObject,
    mut v___y_3684_: *mut leanh::LeanObject,
    mut v___y_3685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
    leanh::lean_dec(v___y_3684_);
    leanh::lean_dec_ref(v___y_3683_);
    leanh::lean_dec(v___y_3682_);
    leanh::lean_dec_ref(v___y_3681_);
    return v_res_3686_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(
    mut v_msg_3687_: *mut leanh::LeanObject,
    mut v___y_3688_: *mut leanh::LeanObject,
    mut v___y_3689_: *mut leanh::LeanObject,
    mut v___y_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3693_ = leanh::lean_ctor_get(v___y_3690_, 5);
                v___x_3694_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
                v_a_3695_ = leanh::lean_ctor_get(v___x_3694_, 0);
                v_isSharedCheck_3703_ = (!leanh::lean_is_exclusive(v___x_3694_)) as u8;
                if v_isSharedCheck_3703_ == 0 {
                    v___x_3697_ = v___x_3694_;
                    v_isShared_3698_ = v_isSharedCheck_3703_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3695_);
                    leanh::lean_dec(v___x_3694_);
                    v___x_3697_ = leanh::lean_box(0);
                    v_isShared_3698_ = v_isSharedCheck_3703_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3693_);
                v___x_3699_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3699_, 0, v_ref_3693_);
                leanh::lean_ctor_set(v___x_3699_, 1, v_a_3695_);
                if v_isShared_3698_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3697_, 1);
                    leanh::lean_ctor_set(v___x_3697_, 0, v___x_3699_);
                    v___x_3701_ = v___x_3697_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3702_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
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
    mut v_msg_3704_: *mut leanh::LeanObject,
    mut v___y_3705_: *mut leanh::LeanObject,
    mut v___y_3706_: *mut leanh::LeanObject,
    mut v___y_3707_: *mut leanh::LeanObject,
    mut v___y_3708_: *mut leanh::LeanObject,
    mut v___y_3709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3710_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
    leanh::lean_dec(v___y_3708_);
    leanh::lean_dec_ref(v___y_3707_);
    leanh::lean_dec(v___y_3706_);
    leanh::lean_dec_ref(v___y_3705_);
    return v_res_3710_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_ref_3711_: *mut leanh::LeanObject,
    mut v_msg_3712_: *mut leanh::LeanObject,
    mut v___y_3713_: *mut leanh::LeanObject,
    mut v___y_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___y_3717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3731_: u8 = 0;
    let mut v_cancelTk_x3f_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3733_: u8 = 0;
    let mut v_inheritedTraceOptions_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3719_ = leanh::lean_ctor_get(v___y_3716_, 0);
    v_fileMap_3720_ = leanh::lean_ctor_get(v___y_3716_, 1);
    v_options_3721_ = leanh::lean_ctor_get(v___y_3716_, 2);
    v_currRecDepth_3722_ = leanh::lean_ctor_get(v___y_3716_, 3);
    v_maxRecDepth_3723_ = leanh::lean_ctor_get(v___y_3716_, 4);
    v_ref_3724_ = leanh::lean_ctor_get(v___y_3716_, 5);
    v_currNamespace_3725_ = leanh::lean_ctor_get(v___y_3716_, 6);
    v_openDecls_3726_ = leanh::lean_ctor_get(v___y_3716_, 7);
    v_initHeartbeats_3727_ = leanh::lean_ctor_get(v___y_3716_, 8);
    v_maxHeartbeats_3728_ = leanh::lean_ctor_get(v___y_3716_, 9);
    v_quotContext_3729_ = leanh::lean_ctor_get(v___y_3716_, 10);
    v_currMacroScope_3730_ = leanh::lean_ctor_get(v___y_3716_, 11);
    v_diag_3731_ = leanh::lean_ctor_get_uint8(
        v___y_3716_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3732_ = leanh::lean_ctor_get(v___y_3716_, 12);
    v_suppressElabErrors_3733_ = leanh::lean_ctor_get_uint8(
        v___y_3716_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3734_ = leanh::lean_ctor_get(v___y_3716_, 13);
    v_ref_3735_ = l_Lean_replaceRef(v_ref_3711_, v_ref_3724_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3734_);
    leanh::lean_inc(v_cancelTk_x3f_3732_);
    leanh::lean_inc(v_currMacroScope_3730_);
    leanh::lean_inc(v_quotContext_3729_);
    leanh::lean_inc(v_maxHeartbeats_3728_);
    leanh::lean_inc(v_initHeartbeats_3727_);
    leanh::lean_inc(v_openDecls_3726_);
    leanh::lean_inc(v_currNamespace_3725_);
    leanh::lean_inc(v_maxRecDepth_3723_);
    leanh::lean_inc(v_currRecDepth_3722_);
    leanh::lean_inc_ref(v_options_3721_);
    leanh::lean_inc_ref(v_fileMap_3720_);
    leanh::lean_inc_ref(v_fileName_3719_);
    v___x_3736_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3736_, 0, v_fileName_3719_);
    leanh::lean_ctor_set(v___x_3736_, 1, v_fileMap_3720_);
    leanh::lean_ctor_set(v___x_3736_, 2, v_options_3721_);
    leanh::lean_ctor_set(v___x_3736_, 3, v_currRecDepth_3722_);
    leanh::lean_ctor_set(v___x_3736_, 4, v_maxRecDepth_3723_);
    leanh::lean_ctor_set(v___x_3736_, 5, v_ref_3735_);
    leanh::lean_ctor_set(v___x_3736_, 6, v_currNamespace_3725_);
    leanh::lean_ctor_set(v___x_3736_, 7, v_openDecls_3726_);
    leanh::lean_ctor_set(v___x_3736_, 8, v_initHeartbeats_3727_);
    leanh::lean_ctor_set(v___x_3736_, 9, v_maxHeartbeats_3728_);
    leanh::lean_ctor_set(v___x_3736_, 10, v_quotContext_3729_);
    leanh::lean_ctor_set(v___x_3736_, 11, v_currMacroScope_3730_);
    leanh::lean_ctor_set(v___x_3736_, 12, v_cancelTk_x3f_3732_);
    leanh::lean_ctor_set(v___x_3736_, 13, v_inheritedTraceOptions_3734_);
    leanh::lean_ctor_set_uint8(
        v___x_3736_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3731_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3736_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3733_,
    );
    v___x_3737_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_3712_, v___y_3714_, v___y_3715_, v___x_3736_, v___y_3717_);
    leanh::lean_dec_ref_known(v___x_3736_, 14);
    return v___x_3737_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_ref_3738_: *mut leanh::LeanObject,
    mut v_msg_3739_: *mut leanh::LeanObject,
    mut v___y_3740_: *mut leanh::LeanObject,
    mut v___y_3741_: *mut leanh::LeanObject,
    mut v___y_3742_: *mut leanh::LeanObject,
    mut v___y_3743_: *mut leanh::LeanObject,
    mut v___y_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3746_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3738_, v_msg_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
    leanh::lean_dec(v___y_3744_);
    leanh::lean_dec_ref(v___y_3743_);
    leanh::lean_dec(v___y_3742_);
    leanh::lean_dec_ref(v___y_3741_);
    leanh::lean_dec_ref(v___y_3740_);
    leanh::lean_dec(v_ref_3738_);
    return v_res_3746_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3747_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3747_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3748_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
    v___x_3749_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3749_, 0, v___x_3748_);
    return v___x_3749_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3750_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_3751_ = leanh::lean_unsigned_to_nat(0);
    v___x_3752_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3752_, 0, v___x_3751_);
    leanh::lean_ctor_set(v___x_3752_, 1, v___x_3751_);
    leanh::lean_ctor_set(v___x_3752_, 2, v___x_3751_);
    leanh::lean_ctor_set(v___x_3752_, 3, v___x_3751_);
    leanh::lean_ctor_set(v___x_3752_, 4, v___x_3750_);
    leanh::lean_ctor_set(v___x_3752_, 5, v___x_3750_);
    leanh::lean_ctor_set(v___x_3752_, 6, v___x_3750_);
    leanh::lean_ctor_set(v___x_3752_, 7, v___x_3750_);
    leanh::lean_ctor_set(v___x_3752_, 8, v___x_3750_);
    leanh::lean_ctor_set(v___x_3752_, 9, v___x_3750_);
    return v___x_3752_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3753_ = leanh::lean_unsigned_to_nat(32);
    v___x_3754_ = lean_mk_empty_array_with_capacity(v___x_3753_);
    v___x_3755_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3755_, 0, v___x_3754_);
    return v___x_3755_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3756_: usize = 0;
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3756_ = 5usize;
    v___x_3757_ = leanh::lean_unsigned_to_nat(0);
    v___x_3758_ = leanh::lean_unsigned_to_nat(32);
    v___x_3759_ = lean_mk_empty_array_with_capacity(v___x_3758_);
    v___x_3760_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
    v___x_3761_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3761_, 0, v___x_3760_);
    leanh::lean_ctor_set(v___x_3761_, 1, v___x_3759_);
    leanh::lean_ctor_set(v___x_3761_, 2, v___x_3757_);
    leanh::lean_ctor_set(v___x_3761_, 3, v___x_3757_);
    leanh::lean_ctor_set_usize(v___x_3761_, 4, v___x_3756_);
    return v___x_3761_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3762_ = leanh::lean_box(1);
    v___x_3763_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
    v___x_3764_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
    v___x_3765_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3765_, 0, v___x_3764_);
    leanh::lean_ctor_set(v___x_3765_, 1, v___x_3763_);
    leanh::lean_ctor_set(v___x_3765_, 2, v___x_3762_);
    return v___x_3765_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3767_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6;
    v___x_3768_ = l_Lean_stringToMessageData(v___x_3767_);
    return v___x_3768_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3770_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8;
    v___x_3771_ = l_Lean_stringToMessageData(v___x_3770_);
    return v___x_3771_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3773_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10;
    v___x_3774_ = l_Lean_stringToMessageData(v___x_3773_);
    return v___x_3774_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12;
    v___x_3777_ = l_Lean_stringToMessageData(v___x_3776_);
    return v___x_3777_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__14;
    v___x_3780_ = l_Lean_stringToMessageData(v___x_3779_);
    return v___x_3780_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3782_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__16;
    v___x_3783_ = l_Lean_stringToMessageData(v___x_3782_);
    return v___x_3783_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__18;
    v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_msg_3787_: *mut leanh::LeanObject,
    mut v_declHint_3788_: *mut leanh::LeanObject,
    mut v___y_3789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: u8 = 0;
    let mut v_isExporting_3794_: u8 = 0;
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3816_: u8 = 0;
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3791_ = lean_st_ref_get(v___y_3789_);
                v_env_3792_ = leanh::lean_ctor_get(v___x_3791_, 0);
                leanh::lean_inc_ref(v_env_3792_);
                leanh::lean_dec(v___x_3791_);
                v___x_3793_ = l_Lean_Name_isAnonymous(v_declHint_3788_);
                if v___x_3793_ == 0 {
                    v_isExporting_3794_ = leanh::lean_ctor_get_uint8(
                        v_env_3792_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3794_ == 0 {
                        leanh::lean_dec_ref(v_env_3792_);
                        leanh::lean_dec(v_declHint_3788_);
                        v___x_3795_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3795_, 0, v_msg_3787_);
                        return v___x_3795_;
                    } else {
                        leanh::lean_inc_ref(v_env_3792_);
                        v___x_3796_ = l_Lean_Environment_setExporting(v_env_3792_, v___x_3793_);
                        leanh::lean_inc(v_declHint_3788_);
                        leanh::lean_inc_ref(v___x_3796_);
                        v___x_3797_ = l_Lean_Environment_contains(
                            v___x_3796_,
                            v_declHint_3788_,
                            v_isExporting_3794_,
                        );
                        if v___x_3797_ == 0 {
                            leanh::lean_dec_ref(v___x_3796_);
                            leanh::lean_dec_ref(v_env_3792_);
                            leanh::lean_dec(v_declHint_3788_);
                            v___x_3798_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3798_, 0, v_msg_3787_);
                            return v___x_3798_;
                        } else {
                            v___x_3799_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
                            v___x_3800_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
                            v___x_3801_ = l_Lean_Options_empty;
                            v___x_3802_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3802_, 0, v___x_3796_);
                            leanh::lean_ctor_set(v___x_3802_, 1, v___x_3799_);
                            leanh::lean_ctor_set(v___x_3802_, 2, v___x_3800_);
                            leanh::lean_ctor_set(v___x_3802_, 3, v___x_3801_);
                            leanh::lean_inc(v_declHint_3788_);
                            v___x_3803_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3788_, v___x_3793_);
                            v_c_3804_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3804_, 0, v___x_3802_);
                            leanh::lean_ctor_set(v_c_3804_, 1, v___x_3803_);
                            v___x_3805_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3792_,
                                v_declHint_3788_,
                            );
                            if leanh::lean_obj_tag(v___x_3805_) == 0 {
                                leanh::lean_dec_ref(v_env_3792_);
                                leanh::lean_dec(v_declHint_3788_);
                                v___x_3806_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                                v___x_3807_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3807_, 0, v___x_3806_);
                                leanh::lean_ctor_set(v___x_3807_, 1, v_c_3804_);
                                v___x_3808_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
                                v___x_3809_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3809_, 0, v___x_3807_);
                                leanh::lean_ctor_set(v___x_3809_, 1, v___x_3808_);
                                v___x_3810_ = l_Lean_MessageData_note(v___x_3809_);
                                v___x_3811_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3811_, 0, v_msg_3787_);
                                leanh::lean_ctor_set(v___x_3811_, 1, v___x_3810_);
                                v___x_3812_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3812_, 0, v___x_3811_);
                                return v___x_3812_;
                            } else {
                                v_val_3813_ = leanh::lean_ctor_get(v___x_3805_, 0);
                                v_isSharedCheck_3848_ =
                                    (!leanh::lean_is_exclusive(v___x_3805_)) as u8;
                                if v_isSharedCheck_3848_ == 0 {
                                    v___x_3815_ = v___x_3805_;
                                    v_isShared_3816_ = v_isSharedCheck_3848_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3813_);
                                    leanh::lean_dec(v___x_3805_);
                                    v___x_3815_ = leanh::lean_box(0);
                                    v_isShared_3816_ = v_isSharedCheck_3848_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3792_);
                    leanh::lean_dec(v_declHint_3788_);
                    v___x_3849_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3849_, 0, v_msg_3787_);
                    return v___x_3849_;
                }
            }
            1 => {
                v___x_3817_ = leanh::lean_box(0);
                v___x_3818_ = l_Lean_Environment_header(v_env_3792_);
                leanh::lean_dec_ref(v_env_3792_);
                v___x_3819_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3818_);
                v_mod_3820_ = lean_array_get(v___x_3817_, v___x_3819_, v_val_3813_);
                leanh::lean_dec(v_val_3813_);
                leanh::lean_dec_ref(v___x_3819_);
                v___x_3821_ = l_Lean_isPrivateName(v_declHint_3788_);
                leanh::lean_dec(v_declHint_3788_);
                if v___x_3821_ == 0 {
                    v___x_3822_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
                    v___x_3823_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3823_, 0, v___x_3822_);
                    leanh::lean_ctor_set(v___x_3823_, 1, v_c_3804_);
                    v___x_3824_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
                    v___x_3825_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3825_, 0, v___x_3823_);
                    leanh::lean_ctor_set(v___x_3825_, 1, v___x_3824_);
                    v___x_3826_ = l_Lean_MessageData_ofName(v_mod_3820_);
                    v___x_3827_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3827_, 0, v___x_3825_);
                    leanh::lean_ctor_set(v___x_3827_, 1, v___x_3826_);
                    v___x_3828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
                    v___x_3829_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3829_, 0, v___x_3827_);
                    leanh::lean_ctor_set(v___x_3829_, 1, v___x_3828_);
                    v___x_3830_ = l_Lean_MessageData_note(v___x_3829_);
                    v___x_3831_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3831_, 0, v_msg_3787_);
                    leanh::lean_ctor_set(v___x_3831_, 1, v___x_3830_);
                    if v_isShared_3816_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3815_, 0);
                        leanh::lean_ctor_set(v___x_3815_, 0, v___x_3831_);
                        v___x_3833_ = v___x_3815_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3834_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
                        v___x_3833_ = v_reuseFailAlloc_3834_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3835_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                    v___x_3836_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3836_, 0, v___x_3835_);
                    leanh::lean_ctor_set(v___x_3836_, 1, v_c_3804_);
                    v___x_3837_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
                    v___x_3838_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3838_, 0, v___x_3836_);
                    leanh::lean_ctor_set(v___x_3838_, 1, v___x_3837_);
                    v___x_3839_ = l_Lean_MessageData_ofName(v_mod_3820_);
                    v___x_3840_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3840_, 0, v___x_3838_);
                    leanh::lean_ctor_set(v___x_3840_, 1, v___x_3839_);
                    v___x_3841_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
                    v___x_3842_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3842_, 0, v___x_3840_);
                    leanh::lean_ctor_set(v___x_3842_, 1, v___x_3841_);
                    v___x_3843_ = l_Lean_MessageData_note(v___x_3842_);
                    v___x_3844_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3844_, 0, v_msg_3787_);
                    leanh::lean_ctor_set(v___x_3844_, 1, v___x_3843_);
                    if v_isShared_3816_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3815_, 0);
                        leanh::lean_ctor_set(v___x_3815_, 0, v___x_3844_);
                        v___x_3846_ = v___x_3815_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
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
    mut v_msg_3850_: *mut leanh::LeanObject,
    mut v_declHint_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
    mut v___y_3853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3854_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_3850_, v_declHint_3851_, v___y_3852_);
    leanh::lean_dec(v___y_3852_);
    return v_res_3854_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_3855_: *mut leanh::LeanObject,
    mut v_declHint_3856_: *mut leanh::LeanObject,
    mut v___y_3857_: *mut leanh::LeanObject,
    mut v___y_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
    mut v___y_3861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3863_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_3855_, v_declHint_3856_, v___y_3861_);
                v_a_3864_ = leanh::lean_ctor_get(v___x_3863_, 0);
                v_isSharedCheck_3873_ = (!leanh::lean_is_exclusive(v___x_3863_)) as u8;
                if v_isSharedCheck_3873_ == 0 {
                    v___x_3866_ = v___x_3863_;
                    v_isShared_3867_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3864_);
                    leanh::lean_dec(v___x_3863_);
                    v___x_3866_ = leanh::lean_box(0);
                    v_isShared_3867_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3868_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3869_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3869_, 0, v___x_3868_);
                leanh::lean_ctor_set(v___x_3869_, 1, v_a_3864_);
                if v_isShared_3867_ == 0 {
                    leanh::lean_ctor_set(v___x_3866_, 0, v___x_3869_);
                    v___x_3871_ = v___x_3866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3872_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3869_);
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
    mut v_msg_3874_: *mut leanh::LeanObject,
    mut v_declHint_3875_: *mut leanh::LeanObject,
    mut v___y_3876_: *mut leanh::LeanObject,
    mut v___y_3877_: *mut leanh::LeanObject,
    mut v___y_3878_: *mut leanh::LeanObject,
    mut v___y_3879_: *mut leanh::LeanObject,
    mut v___y_3880_: *mut leanh::LeanObject,
    mut v___y_3881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3882_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3874_, v_declHint_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
    leanh::lean_dec(v___y_3880_);
    leanh::lean_dec_ref(v___y_3879_);
    leanh::lean_dec(v___y_3878_);
    leanh::lean_dec_ref(v___y_3877_);
    leanh::lean_dec_ref(v___y_3876_);
    return v_res_3882_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_ref_3883_: *mut leanh::LeanObject,
    mut v_msg_3884_: *mut leanh::LeanObject,
    mut v_declHint_3885_: *mut leanh::LeanObject,
    mut v___y_3886_: *mut leanh::LeanObject,
    mut v___y_3887_: *mut leanh::LeanObject,
    mut v___y_3888_: *mut leanh::LeanObject,
    mut v___y_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3892_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3884_, v_declHint_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
    v_a_3893_ = leanh::lean_ctor_get(v___x_3892_, 0);
    leanh::lean_inc(v_a_3893_);
    leanh::lean_dec_ref(v___x_3892_);
    v___x_3894_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_3883_, v_a_3893_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
    return v___x_3894_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_ref_3895_: *mut leanh::LeanObject,
    mut v_msg_3896_: *mut leanh::LeanObject,
    mut v_declHint_3897_: *mut leanh::LeanObject,
    mut v___y_3898_: *mut leanh::LeanObject,
    mut v___y_3899_: *mut leanh::LeanObject,
    mut v___y_3900_: *mut leanh::LeanObject,
    mut v___y_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
    mut v___y_3903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_3895_, v_msg_3896_, v_declHint_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
    leanh::lean_dec(v___y_3902_);
    leanh::lean_dec_ref(v___y_3901_);
    leanh::lean_dec(v___y_3900_);
    leanh::lean_dec_ref(v___y_3899_);
    leanh::lean_dec_ref(v___y_3898_);
    leanh::lean_dec(v_ref_3895_);
    return v_res_3904_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3906_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0;
    v___x_3907_ = l_Lean_stringToMessageData(v___x_3906_);
    return v___x_3907_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3909_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2;
    v___x_3910_ = l_Lean_stringToMessageData(v___x_3909_);
    return v___x_3910_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_3911_: *mut leanh::LeanObject,
    mut v_constName_3912_: *mut leanh::LeanObject,
    mut v___y_3913_: *mut leanh::LeanObject,
    mut v___y_3914_: *mut leanh::LeanObject,
    mut v___y_3915_: *mut leanh::LeanObject,
    mut v___y_3916_: *mut leanh::LeanObject,
    mut v___y_3917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: u8 = 0;
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3919_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
    v___x_3920_ = 0;
    leanh::lean_inc(v_constName_3912_);
    v___x_3921_ = l_Lean_MessageData_ofConstName(v_constName_3912_, v___x_3920_);
    v___x_3922_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3922_, 0, v___x_3919_);
    leanh::lean_ctor_set(v___x_3922_, 1, v___x_3921_);
    v___x_3923_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
    v___x_3924_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3924_, 0, v___x_3922_);
    leanh::lean_ctor_set(v___x_3924_, 1, v___x_3923_);
    v___x_3925_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_3911_, v___x_3924_, v_constName_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
    return v___x_3925_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_3926_: *mut leanh::LeanObject,
    mut v_constName_3927_: *mut leanh::LeanObject,
    mut v___y_3928_: *mut leanh::LeanObject,
    mut v___y_3929_: *mut leanh::LeanObject,
    mut v___y_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3934_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3926_, v_constName_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
    leanh::lean_dec(v___y_3932_);
    leanh::lean_dec_ref(v___y_3931_);
    leanh::lean_dec(v___y_3930_);
    leanh::lean_dec_ref(v___y_3929_);
    leanh::lean_dec_ref(v___y_3928_);
    leanh::lean_dec(v_ref_3926_);
    return v_res_3934_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_constName_3935_: *mut leanh::LeanObject,
    mut v___y_3936_: *mut leanh::LeanObject,
    mut v___y_3937_: *mut leanh::LeanObject,
    mut v___y_3938_: *mut leanh::LeanObject,
    mut v___y_3939_: *mut leanh::LeanObject,
    mut v___y_3940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3942_ = leanh::lean_ctor_get(v___y_3939_, 5);
    v___x_3943_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3942_, v_constName_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
    return v___x_3943_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_constName_3944_: *mut leanh::LeanObject,
    mut v___y_3945_: *mut leanh::LeanObject,
    mut v___y_3946_: *mut leanh::LeanObject,
    mut v___y_3947_: *mut leanh::LeanObject,
    mut v___y_3948_: *mut leanh::LeanObject,
    mut v___y_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3951_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
    leanh::lean_dec(v___y_3949_);
    leanh::lean_dec_ref(v___y_3948_);
    leanh::lean_dec(v___y_3947_);
    leanh::lean_dec_ref(v___y_3946_);
    leanh::lean_dec_ref(v___y_3945_);
    return v_res_3951_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(
    mut v_constName_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
    mut v___y_3956_: *mut leanh::LeanObject,
    mut v___y_3957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: u8 = 0;
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3967_: u8 = 0;
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3959_ = lean_st_ref_get(v___y_3957_);
                v_env_3960_ = leanh::lean_ctor_get(v___x_3959_, 0);
                leanh::lean_inc_ref(v_env_3960_);
                leanh::lean_dec(v___x_3959_);
                v___x_3961_ = 0;
                leanh::lean_inc(v_constName_3952_);
                v___x_3962_ =
                    l_Lean_Environment_find_x3f(v_env_3960_, v_constName_3952_, v___x_3961_);
                if leanh::lean_obj_tag(v___x_3962_) == 0 {
                    v___x_3963_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
                    return v___x_3963_;
                } else {
                    leanh::lean_dec(v_constName_3952_);
                    v_val_3964_ = leanh::lean_ctor_get(v___x_3962_, 0);
                    v_isSharedCheck_3971_ = (!leanh::lean_is_exclusive(v___x_3962_)) as u8;
                    if v_isSharedCheck_3971_ == 0 {
                        v___x_3966_ = v___x_3962_;
                        v_isShared_3967_ = v_isSharedCheck_3971_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3964_);
                        leanh::lean_dec(v___x_3962_);
                        v___x_3966_ = leanh::lean_box(0);
                        v_isShared_3967_ = v_isSharedCheck_3971_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3967_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3966_, 0);
                    v___x_3969_ = v___x_3966_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3970_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_val_3964_);
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
    mut v_constName_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
    mut v___y_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_constName_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
    leanh::lean_dec(v___y_3977_);
    leanh::lean_dec_ref(v___y_3976_);
    leanh::lean_dec(v___y_3975_);
    leanh::lean_dec_ref(v___y_3974_);
    leanh::lean_dec_ref(v___y_3973_);
    return v_res_3979_;
}
pub unsafe fn l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(
    mut v_declName_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
    mut v___y_3985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4001_: u8 = 0;
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut v_isSharedCheck_4014_: u8 = 0;
    let mut v_unused_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4019_: u8 = 0;
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_3980_);
                v___x_3987_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0(v_declName_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
                if leanh::lean_obj_tag(v___x_3987_) == 0 {
                    v_isSharedCheck_4014_ = (!leanh::lean_is_exclusive(v___x_3987_)) as u8;
                    if v_isSharedCheck_4014_ == 0 {
                        v_unused_4015_ = leanh::lean_ctor_get(v___x_3987_, 0);
                        leanh::lean_dec(v_unused_4015_);
                        v___x_3989_ = v___x_3987_;
                        v_isShared_3990_ = v_isSharedCheck_4014_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3987_);
                        v___x_3989_ = leanh::lean_box(0);
                        v_isShared_3990_ = v_isSharedCheck_4014_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_3980_);
                    v_a_4016_ = leanh::lean_ctor_get(v___x_3987_, 0);
                    v_isSharedCheck_4023_ = (!leanh::lean_is_exclusive(v___x_3987_)) as u8;
                    if v_isSharedCheck_4023_ == 0 {
                        v___x_4018_ = v___x_3987_;
                        v_isShared_4019_ = v_isSharedCheck_4023_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4016_);
                        leanh::lean_dec(v___x_3987_);
                        v___x_4018_ = leanh::lean_box(0);
                        v_isShared_4019_ = v_isSharedCheck_4023_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3991_ = lean_st_ref_get(v___y_3985_);
                v_env_3992_ = leanh::lean_ctor_get(v___x_3991_, 0);
                leanh::lean_inc_ref(v_env_3992_);
                leanh::lean_dec(v___x_3991_);
                v___x_3993_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3992_, v_declName_3980_);
                leanh::lean_dec(v_declName_3980_);
                leanh::lean_dec_ref(v_env_3992_);
                if leanh::lean_obj_tag(v___x_3993_) == 0 {
                    v___x_3994_ = leanh::lean_box(0);
                    if v_isShared_3990_ == 0 {
                        leanh::lean_ctor_set(v___x_3989_, 0, v___x_3994_);
                        v___x_3996_ = v___x_3989_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3994_);
                        v___x_3996_ = v_reuseFailAlloc_3997_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3998_ = leanh::lean_ctor_get(v___x_3993_, 0);
                    v_isSharedCheck_4013_ = (!leanh::lean_is_exclusive(v___x_3993_)) as u8;
                    if v_isSharedCheck_4013_ == 0 {
                        v___x_4000_ = v___x_3993_;
                        v_isShared_4001_ = v_isSharedCheck_4013_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3998_);
                        leanh::lean_dec(v___x_3993_);
                        v___x_4000_ = leanh::lean_box(0);
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
                v_env_4003_ = leanh::lean_ctor_get(v___x_4002_, 0);
                leanh::lean_inc_ref(v_env_4003_);
                leanh::lean_dec(v___x_4002_);
                v___x_4004_ = leanh::lean_box(0);
                v___x_4005_ = l_Lean_Environment_allImportedModuleNames(v_env_4003_);
                leanh::lean_dec_ref(v_env_4003_);
                v___x_4006_ = lean_array_get(v___x_4004_, v___x_4005_, v_val_3998_);
                leanh::lean_dec(v_val_3998_);
                leanh::lean_dec_ref(v___x_4005_);
                if v_isShared_4001_ == 0 {
                    leanh::lean_ctor_set(v___x_4000_, 0, v___x_4006_);
                    v___x_4008_ = v___x_4000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4012_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4006_);
                    v___x_4008_ = v_reuseFailAlloc_4012_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3990_ == 0 {
                    leanh::lean_ctor_set(v___x_3989_, 0, v___x_4008_);
                    v___x_4010_ = v___x_3989_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4008_);
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
                    v_reuseFailAlloc_4022_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
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
    mut v_declName_4024_: *mut leanh::LeanObject,
    mut v___y_4025_: *mut leanh::LeanObject,
    mut v___y_4026_: *mut leanh::LeanObject,
    mut v___y_4027_: *mut leanh::LeanObject,
    mut v___y_4028_: *mut leanh::LeanObject,
    mut v___y_4029_: *mut leanh::LeanObject,
    mut v___y_4030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4031_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
    leanh::lean_dec(v___y_4029_);
    leanh::lean_dec_ref(v___y_4028_);
    leanh::lean_dec(v___y_4027_);
    leanh::lean_dec_ref(v___y_4026_);
    leanh::lean_dec_ref(v___y_4025_);
    return v_res_4031_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(
    mut v_declName_4032_: *mut leanh::LeanObject,
    mut v_a_4033_: *mut leanh::LeanObject,
    mut v_a_4034_: *mut leanh::LeanObject,
    mut v_a_4035_: *mut leanh::LeanObject,
    mut v_a_4036_: *mut leanh::LeanObject,
    mut v_a_4037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4043_: u8 = 0;
    let mut v_doc_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v_val_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4064_: u8 = 0;
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_a_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v_ref_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut v_isSharedCheck_4094_: u8 = 0;
    let mut v_a_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4098_: u8 = 0;
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4039_ = l_Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0(v_declName_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
                if leanh::lean_obj_tag(v___x_4039_) == 0 {
                    v_a_4040_ = leanh::lean_ctor_get(v___x_4039_, 0);
                    v_isSharedCheck_4094_ = (!leanh::lean_is_exclusive(v___x_4039_)) as u8;
                    if v_isSharedCheck_4094_ == 0 {
                        v___x_4042_ = v___x_4039_;
                        v_isShared_4043_ = v_isSharedCheck_4094_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4040_);
                        leanh::lean_dec(v___x_4039_);
                        v___x_4042_ = leanh::lean_box(0);
                        v_isShared_4043_ = v_isSharedCheck_4094_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4095_ = leanh::lean_ctor_get(v___x_4039_, 0);
                    v_isSharedCheck_4102_ = (!leanh::lean_is_exclusive(v___x_4039_)) as u8;
                    if v_isSharedCheck_4102_ == 0 {
                        v___x_4097_ = v___x_4039_;
                        v_isShared_4098_ = v_isSharedCheck_4102_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4095_);
                        leanh::lean_dec(v___x_4039_);
                        v___x_4097_ = leanh::lean_box(0);
                        v_isShared_4098_ = v_isSharedCheck_4102_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4040_) == 0 {
                    v_doc_4044_ = leanh::lean_ctor_get(v_a_4033_, 0);
                    v_uri_4045_ = leanh::lean_ctor_get(v_doc_4044_, 0);
                    v_mod_4046_ = leanh::lean_ctor_get(v_doc_4044_, 1);
                    leanh::lean_inc_ref(v_uri_4045_);
                    leanh::lean_inc(v_mod_4046_);
                    v___x_4047_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4047_, 0, v_mod_4046_);
                    leanh::lean_ctor_set(v___x_4047_, 1, v_uri_4045_);
                    v___x_4048_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4048_, 0, v___x_4047_);
                    if v_isShared_4043_ == 0 {
                        leanh::lean_ctor_set(v___x_4042_, 0, v___x_4048_);
                        v___x_4050_ = v___x_4042_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4048_);
                        v___x_4050_ = v_reuseFailAlloc_4051_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4042_);
                    v_val_4052_ = leanh::lean_ctor_get(v_a_4040_, 0);
                    v_isSharedCheck_4093_ = (!leanh::lean_is_exclusive(v_a_4040_)) as u8;
                    if v_isSharedCheck_4093_ == 0 {
                        v___x_4054_ = v_a_4040_;
                        v_isShared_4055_ = v_isSharedCheck_4093_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4052_);
                        leanh::lean_dec(v_a_4040_);
                        v___x_4054_ = leanh::lean_box(0);
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
                leanh::lean_inc(v_val_4052_);
                v___x_4056_ = l_Lean_Server_documentUriFromModule_x3f(v_val_4052_);
                if leanh::lean_obj_tag(v___x_4056_) == 0 {
                    leanh::lean_del_object(v___x_4054_);
                    v_a_4057_ = leanh::lean_ctor_get(v___x_4056_, 0);
                    v_isSharedCheck_4077_ = (!leanh::lean_is_exclusive(v___x_4056_)) as u8;
                    if v_isSharedCheck_4077_ == 0 {
                        v___x_4059_ = v___x_4056_;
                        v_isShared_4060_ = v_isSharedCheck_4077_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4057_);
                        leanh::lean_dec(v___x_4056_);
                        v___x_4059_ = leanh::lean_box(0);
                        v_isShared_4060_ = v_isSharedCheck_4077_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_val_4052_);
                    v_a_4078_ = leanh::lean_ctor_get(v___x_4056_, 0);
                    v_isSharedCheck_4092_ = (!leanh::lean_is_exclusive(v___x_4056_)) as u8;
                    if v_isSharedCheck_4092_ == 0 {
                        v___x_4080_ = v___x_4056_;
                        v_isShared_4081_ = v_isSharedCheck_4092_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4078_);
                        leanh::lean_dec(v___x_4056_);
                        v___x_4080_ = leanh::lean_box(0);
                        v_isShared_4081_ = v_isSharedCheck_4092_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                if leanh::lean_obj_tag(v_a_4057_) == 1 {
                    v_val_4061_ = leanh::lean_ctor_get(v_a_4057_, 0);
                    v_isSharedCheck_4072_ = (!leanh::lean_is_exclusive(v_a_4057_)) as u8;
                    if v_isSharedCheck_4072_ == 0 {
                        v___x_4063_ = v_a_4057_;
                        v_isShared_4064_ = v_isSharedCheck_4072_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4061_);
                        leanh::lean_dec(v_a_4057_);
                        v___x_4063_ = leanh::lean_box(0);
                        v_isShared_4064_ = v_isSharedCheck_4072_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4057_);
                    leanh::lean_dec(v_val_4052_);
                    v___x_4073_ = leanh::lean_box(0);
                    if v_isShared_4060_ == 0 {
                        leanh::lean_ctor_set(v___x_4059_, 0, v___x_4073_);
                        v___x_4075_ = v___x_4059_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4076_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
                        v___x_4075_ = v_reuseFailAlloc_4076_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4065_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4065_, 0, v_val_4052_);
                leanh::lean_ctor_set(v___x_4065_, 1, v_val_4061_);
                if v_isShared_4064_ == 0 {
                    leanh::lean_ctor_set(v___x_4063_, 0, v___x_4065_);
                    v___x_4067_ = v___x_4063_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4071_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4065_);
                    v___x_4067_ = v_reuseFailAlloc_4071_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4060_ == 0 {
                    leanh::lean_ctor_set(v___x_4059_, 0, v___x_4067_);
                    v___x_4069_ = v___x_4059_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4067_);
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
                v_ref_4082_ = leanh::lean_ctor_get(v_a_4036_, 5);
                v___x_4083_ = lean_io_error_to_string(v_a_4078_);
                if v_isShared_4055_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4054_, 3);
                    leanh::lean_ctor_set(v___x_4054_, 0, v___x_4083_);
                    v___x_4085_ = v___x_4054_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4083_);
                    v___x_4085_ = v_reuseFailAlloc_4091_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4086_ = l_Lean_MessageData_ofFormat(v___x_4085_);
                leanh::lean_inc(v_ref_4082_);
                v___x_4087_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4087_, 0, v_ref_4082_);
                leanh::lean_ctor_set(v___x_4087_, 1, v___x_4086_);
                if v_isShared_4081_ == 0 {
                    leanh::lean_ctor_set(v___x_4080_, 0, v___x_4087_);
                    v___x_4089_ = v___x_4080_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4090_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
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
                    v_reuseFailAlloc_4101_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
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
    mut v_declName_4103_: *mut leanh::LeanObject,
    mut v_a_4104_: *mut leanh::LeanObject,
    mut v_a_4105_: *mut leanh::LeanObject,
    mut v_a_4106_: *mut leanh::LeanObject,
    mut v_a_4107_: *mut leanh::LeanObject,
    mut v_a_4108_: *mut leanh::LeanObject,
    mut v_a_4109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4110_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(
        v_declName_4103_,
        v_a_4104_,
        v_a_4105_,
        v_a_4106_,
        v_a_4107_,
        v_a_4108_,
    );
    leanh::lean_dec(v_a_4108_);
    leanh::lean_dec_ref(v_a_4107_);
    leanh::lean_dec(v_a_4106_);
    leanh::lean_dec_ref(v_a_4105_);
    leanh::lean_dec_ref(v_a_4104_);
    return v_res_4110_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4111_: *mut leanh::LeanObject,
    mut v_constName_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
    mut v___y_4115_: *mut leanh::LeanObject,
    mut v___y_4116_: *mut leanh::LeanObject,
    mut v___y_4117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4119_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___redArg(v_constName_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
    return v___x_4119_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4120_: *mut leanh::LeanObject,
    mut v_constName_4121_: *mut leanh::LeanObject,
    mut v___y_4122_: *mut leanh::LeanObject,
    mut v___y_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
    mut v___y_4127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4128_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1(v_00_u03b1_4120_, v_constName_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
    leanh::lean_dec(v___y_4126_);
    leanh::lean_dec_ref(v___y_4125_);
    leanh::lean_dec(v___y_4124_);
    leanh::lean_dec_ref(v___y_4123_);
    leanh::lean_dec_ref(v___y_4122_);
    return v_res_4128_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_4129_: *mut leanh::LeanObject,
    mut v_ref_4130_: *mut leanh::LeanObject,
    mut v_constName_4131_: *mut leanh::LeanObject,
    mut v___y_4132_: *mut leanh::LeanObject,
    mut v___y_4133_: *mut leanh::LeanObject,
    mut v___y_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4138_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4130_, v_constName_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
    return v___x_4138_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_4139_: *mut leanh::LeanObject,
    mut v_ref_4140_: *mut leanh::LeanObject,
    mut v_constName_4141_: *mut leanh::LeanObject,
    mut v___y_4142_: *mut leanh::LeanObject,
    mut v___y_4143_: *mut leanh::LeanObject,
    mut v___y_4144_: *mut leanh::LeanObject,
    mut v___y_4145_: *mut leanh::LeanObject,
    mut v___y_4146_: *mut leanh::LeanObject,
    mut v___y_4147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4148_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_4139_, v_ref_4140_, v_constName_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
    leanh::lean_dec(v___y_4146_);
    leanh::lean_dec_ref(v___y_4145_);
    leanh::lean_dec(v___y_4144_);
    leanh::lean_dec_ref(v___y_4143_);
    leanh::lean_dec_ref(v___y_4142_);
    leanh::lean_dec(v_ref_4140_);
    return v_res_4148_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b1_4149_: *mut leanh::LeanObject,
    mut v_ref_4150_: *mut leanh::LeanObject,
    mut v_msg_4151_: *mut leanh::LeanObject,
    mut v_declHint_4152_: *mut leanh::LeanObject,
    mut v___y_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
    mut v___y_4155_: *mut leanh::LeanObject,
    mut v___y_4156_: *mut leanh::LeanObject,
    mut v___y_4157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ref_4150_, v_msg_4151_, v_declHint_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
    return v___x_4159_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_4160_: *mut leanh::LeanObject,
    mut v_ref_4161_: *mut leanh::LeanObject,
    mut v_msg_4162_: *mut leanh::LeanObject,
    mut v_declHint_4163_: *mut leanh::LeanObject,
    mut v___y_4164_: *mut leanh::LeanObject,
    mut v___y_4165_: *mut leanh::LeanObject,
    mut v___y_4166_: *mut leanh::LeanObject,
    mut v___y_4167_: *mut leanh::LeanObject,
    mut v___y_4168_: *mut leanh::LeanObject,
    mut v___y_4169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4170_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b1_4160_, v_ref_4161_, v_msg_4162_, v_declHint_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
    leanh::lean_dec(v___y_4168_);
    leanh::lean_dec_ref(v___y_4167_);
    leanh::lean_dec(v___y_4166_);
    leanh::lean_dec_ref(v___y_4165_);
    leanh::lean_dec_ref(v___y_4164_);
    leanh::lean_dec(v_ref_4161_);
    return v_res_4170_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(
    mut v_msg_4171_: *mut leanh::LeanObject,
    mut v_declHint_4172_: *mut leanh::LeanObject,
    mut v___y_4173_: *mut leanh::LeanObject,
    mut v___y_4174_: *mut leanh::LeanObject,
    mut v___y_4175_: *mut leanh::LeanObject,
    mut v___y_4176_: *mut leanh::LeanObject,
    mut v___y_4177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4179_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_4171_, v_declHint_4172_, v___y_4177_);
    return v___x_4179_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_msg_4180_: *mut leanh::LeanObject,
    mut v_declHint_4181_: *mut leanh::LeanObject,
    mut v___y_4182_: *mut leanh::LeanObject,
    mut v___y_4183_: *mut leanh::LeanObject,
    mut v___y_4184_: *mut leanh::LeanObject,
    mut v___y_4185_: *mut leanh::LeanObject,
    mut v___y_4186_: *mut leanh::LeanObject,
    mut v___y_4187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_4180_, v_declHint_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
    leanh::lean_dec(v___y_4186_);
    leanh::lean_dec_ref(v___y_4185_);
    leanh::lean_dec(v___y_4184_);
    leanh::lean_dec_ref(v___y_4183_);
    leanh::lean_dec_ref(v___y_4182_);
    return v_res_4188_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b1_4189_: *mut leanh::LeanObject,
    mut v_ref_4190_: *mut leanh::LeanObject,
    mut v_msg_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
    mut v___y_4193_: *mut leanh::LeanObject,
    mut v___y_4194_: *mut leanh::LeanObject,
    mut v___y_4195_: *mut leanh::LeanObject,
    mut v___y_4196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4198_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_4190_, v_msg_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
    return v___x_4198_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_4199_: *mut leanh::LeanObject,
    mut v_ref_4200_: *mut leanh::LeanObject,
    mut v_msg_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: *mut leanh::LeanObject,
    mut v___y_4203_: *mut leanh::LeanObject,
    mut v___y_4204_: *mut leanh::LeanObject,
    mut v___y_4205_: *mut leanh::LeanObject,
    mut v___y_4206_: *mut leanh::LeanObject,
    mut v___y_4207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4208_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_4199_, v_ref_4200_, v_msg_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
    leanh::lean_dec(v___y_4206_);
    leanh::lean_dec_ref(v___y_4205_);
    leanh::lean_dec(v___y_4204_);
    leanh::lean_dec_ref(v___y_4203_);
    leanh::lean_dec_ref(v___y_4202_);
    leanh::lean_dec(v_ref_4200_);
    return v_res_4208_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(
    mut v_00_u03b1_4209_: *mut leanh::LeanObject,
    mut v_msg_4210_: *mut leanh::LeanObject,
    mut v___y_4211_: *mut leanh::LeanObject,
    mut v___y_4212_: *mut leanh::LeanObject,
    mut v___y_4213_: *mut leanh::LeanObject,
    mut v___y_4214_: *mut leanh::LeanObject,
    mut v___y_4215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_4210_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
    return v___x_4217_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_4218_: *mut leanh::LeanObject,
    mut v_msg_4219_: *mut leanh::LeanObject,
    mut v___y_4220_: *mut leanh::LeanObject,
    mut v___y_4221_: *mut leanh::LeanObject,
    mut v___y_4222_: *mut leanh::LeanObject,
    mut v___y_4223_: *mut leanh::LeanObject,
    mut v___y_4224_: *mut leanh::LeanObject,
    mut v___y_4225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4226_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00__private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_4218_, v_msg_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
    leanh::lean_dec(v___y_4224_);
    leanh::lean_dec_ref(v___y_4223_);
    leanh::lean_dec(v___y_4222_);
    leanh::lean_dec_ref(v___y_4221_);
    leanh::lean_dec_ref(v___y_4220_);
    return v_res_4226_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(
    mut v_declName_4227_: *mut leanh::LeanObject,
    mut v___y_4228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = lean_st_ref_get(v___y_4228_);
    v_env_4231_ = leanh::lean_ctor_get(v___x_4230_, 0);
    leanh::lean_inc_ref(v_env_4231_);
    leanh::lean_dec(v___x_4230_);
    v___x_4232_ = l_Lean_isRecCore(v_env_4231_, v_declName_4227_);
    v___x_4233_ = leanh::lean_box((v___x_4232_) as usize);
    v___x_4234_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4234_, 0, v___x_4233_);
    return v___x_4234_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg___boxed(
    mut v_declName_4235_: *mut leanh::LeanObject,
    mut v___y_4236_: *mut leanh::LeanObject,
    mut v___y_4237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4238_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_4235_, v___y_4236_);
    leanh::lean_dec(v___y_4236_);
    return v_res_4238_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(
    mut v_declName_4239_: *mut leanh::LeanObject,
    mut v___y_4240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: u8 = 0;
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = lean_st_ref_get(v___y_4240_);
    v_env_4243_ = leanh::lean_ctor_get(v___x_4242_, 0);
    leanh::lean_inc_ref(v_env_4243_);
    leanh::lean_dec(v___x_4242_);
    v___x_4244_ = lean_st_ref_get(v___y_4240_);
    v_env_4245_ = leanh::lean_ctor_get(v___x_4244_, 0);
    leanh::lean_inc_ref(v_env_4245_);
    leanh::lean_dec(v___x_4244_);
    v___x_4246_ = l_Lean_declRangeExt;
    v_toEnvExtension_4247_ = leanh::lean_ctor_get(v___x_4246_, 0);
    v_asyncMode_4248_ = leanh::lean_ctor_get(v_toEnvExtension_4247_, 2);
    v___x_4249_ = l_Lean_instInhabitedDeclarationRanges_default;
    v___x_4250_ = 0;
    leanh::lean_inc(v_declName_4239_);
    v___x_4251_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_4249_,
        v___x_4246_,
        v_env_4243_,
        v_declName_4239_,
        v_asyncMode_4248_,
        v___x_4250_,
    );
    if leanh::lean_obj_tag(v___x_4251_) == 0 {
        let mut v___x_4252_: u8 = 0;
        let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4252_ = 1;
        v___x_4253_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
            v___x_4249_,
            v___x_4246_,
            v_env_4245_,
            v_declName_4239_,
            v_asyncMode_4248_,
            v___x_4252_,
        );
        v___x_4254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4254_, 0, v___x_4253_);
        return v___x_4254_;
    } else {
        let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_env_4245_);
        leanh::lean_dec(v_declName_4239_);
        v___x_4255_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4255_, 0, v___x_4251_);
        return v___x_4255_;
    }
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg___boxed(
    mut v_declName_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_4256_, v___y_4257_);
    leanh::lean_dec(v___y_4257_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(
    mut v_declName_4260_: *mut leanh::LeanObject,
    mut v___y_4261_: *mut leanh::LeanObject,
    mut v___y_4262_: *mut leanh::LeanObject,
    mut v___y_4263_: *mut leanh::LeanObject,
    mut v___y_4264_: *mut leanh::LeanObject,
    mut v___y_4265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ranges_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4283_: u8 = 0;
    let mut v___x_4284_: u8 = 0;
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___x_4288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4274_ = lean_st_ref_get(v___y_4265_);
                v_env_4275_ = leanh::lean_ctor_get(v___x_4274_, 0);
                leanh::lean_inc_ref_n(v_env_4275_, 2);
                leanh::lean_dec(v___x_4274_);
                leanh::lean_inc_n(v_declName_4260_, 2);
                v___x_4276_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_4260_, v___y_4265_);
                v_a_4277_ = leanh::lean_ctor_get(v___x_4276_, 0);
                leanh::lean_inc(v_a_4277_);
                leanh::lean_dec_ref(v___x_4276_);
                v___x_4287_ = l_Lean_isAuxRecursor(v_env_4275_, v_declName_4260_);
                if v___x_4287_ == 0 {
                    leanh::lean_inc(v_declName_4260_);
                    v___x_4288_ = l_Lean_isNoConfusion(v_env_4275_, v_declName_4260_);
                    v___y_4283_ = v___x_4288_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_4275_);
                    v___y_4283_ = v___x_4287_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_ranges_4268_) == 0 {
                    v___x_4269_ = l_Lean_builtinDeclRanges;
                    v___x_4270_ = lean_st_ref_get(v___x_4269_);
                    v___x_4271_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4270_, v_declName_4260_);
                    leanh::lean_dec(v_declName_4260_);
                    leanh::lean_dec(v___x_4270_);
                    v___x_4272_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4272_, 0, v___x_4271_);
                    return v___x_4272_;
                } else {
                    leanh::lean_dec(v_declName_4260_);
                    v___x_4273_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4273_, 0, v_ranges_4268_);
                    return v___x_4273_;
                }
            }
            2 => {
                v___x_4279_ = l_Lean_Name_getPrefix(v_declName_4260_);
                v___x_4280_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v___x_4279_, v___y_4265_);
                v_a_4281_ = leanh::lean_ctor_get(v___x_4280_, 0);
                leanh::lean_inc(v_a_4281_);
                leanh::lean_dec_ref(v___x_4280_);
                v_ranges_4268_ = v_a_4281_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_4283_ == 0 {
                    v___x_4284_ = (leanh::lean_unbox(v_a_4277_) as u8);
                    leanh::lean_dec(v_a_4277_);
                    if v___x_4284_ == 0 {
                        leanh::lean_inc(v_declName_4260_);
                        v___x_4285_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_4260_, v___y_4265_);
                        v_a_4286_ = leanh::lean_ctor_get(v___x_4285_, 0);
                        leanh::lean_inc(v_a_4286_);
                        leanh::lean_dec_ref(v___x_4285_);
                        v_ranges_4268_ = v_a_4286_;
                        state = 1;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4277_);
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0___boxed(
    mut v_declName_4289_: *mut leanh::LeanObject,
    mut v___y_4290_: *mut leanh::LeanObject,
    mut v___y_4291_: *mut leanh::LeanObject,
    mut v___y_4292_: *mut leanh::LeanObject,
    mut v___y_4293_: *mut leanh::LeanObject,
    mut v___y_4294_: *mut leanh::LeanObject,
    mut v___y_4295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4296_ =
        l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(
            v_declName_4289_,
            v___y_4290_,
            v___y_4291_,
            v___y_4292_,
            v___y_4293_,
            v___y_4294_,
        );
    leanh::lean_dec(v___y_4294_);
    leanh::lean_dec_ref(v___y_4293_);
    leanh::lean_dec(v___y_4292_);
    leanh::lean_dec_ref(v___y_4291_);
    leanh::lean_dec_ref(v___y_4290_);
    return v_res_4296_;
}
pub unsafe fn l_Lean_Server_locationLinksFromDecl(
    mut v_declName_4299_: *mut leanh::LeanObject,
    mut v_a_4300_: *mut leanh::LeanObject,
    mut v_a_4301_: *mut leanh::LeanObject,
    mut v_a_4302_: *mut leanh::LeanObject,
    mut v_a_4303_: *mut leanh::LeanObject,
    mut v_a_4304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v_val_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v_val_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4328_: u8 = 0;
    let mut v_doc_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_originInfo_x3f_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: u8 = 0;
    let mut v___y_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_selectionRange_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4338_: u8 = 0;
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4364_: u8 = 0;
    let mut v_text_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4370_: u8 = 0;
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut v_a_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut v_a_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4306_ = lean_st_ref_get(v_a_4304_);
                v_env_4307_ = leanh::lean_ctor_get(v___x_4306_, 0);
                leanh::lean_inc_ref(v_env_4307_);
                leanh::lean_dec(v___x_4306_);
                v___x_4308_ = 1;
                leanh::lean_inc(v_declName_4299_);
                v___x_4309_ =
                    l_Lean_Environment_contains(v_env_4307_, v_declName_4299_, v___x_4308_);
                if v___x_4309_ == 0 {
                    leanh::lean_dec(v_declName_4299_);
                    v___x_4310_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v___x_4311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4311_, 0, v___x_4310_);
                    return v___x_4311_;
                } else {
                    leanh::lean_inc(v_declName_4299_);
                    v___x_4312_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromDecl_declMod_x3f(v_declName_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
                    if leanh::lean_obj_tag(v___x_4312_) == 0 {
                        v_a_4313_ = leanh::lean_ctor_get(v___x_4312_, 0);
                        v_isSharedCheck_4389_ =
                            (!leanh::lean_is_exclusive(v___x_4312_)) as u8;
                        if v_isSharedCheck_4389_ == 0 {
                            v___x_4315_ = v___x_4312_;
                            v_isShared_4316_ = v_isSharedCheck_4389_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4313_);
                            leanh::lean_dec(v___x_4312_);
                            v___x_4315_ = leanh::lean_box(0);
                            v_isShared_4316_ = v_isSharedCheck_4389_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_4299_);
                        v_a_4390_ = leanh::lean_ctor_get(v___x_4312_, 0);
                        v_isSharedCheck_4397_ =
                            (!leanh::lean_is_exclusive(v___x_4312_)) as u8;
                        if v_isSharedCheck_4397_ == 0 {
                            v___x_4392_ = v___x_4312_;
                            v_isShared_4393_ = v_isSharedCheck_4397_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4390_);
                            leanh::lean_dec(v___x_4312_);
                            v___x_4392_ = leanh::lean_box(0);
                            v_isShared_4393_ = v_isSharedCheck_4397_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4313_) == 1 {
                    leanh::lean_del_object(v___x_4315_);
                    v_val_4317_ = leanh::lean_ctor_get(v_a_4313_, 0);
                    leanh::lean_inc(v_val_4317_);
                    leanh::lean_dec_ref_known(v_a_4313_, 1);
                    v_fst_4318_ = leanh::lean_ctor_get(v_val_4317_, 0);
                    leanh::lean_inc(v_fst_4318_);
                    v_snd_4319_ = leanh::lean_ctor_get(v_val_4317_, 1);
                    leanh::lean_inc(v_snd_4319_);
                    leanh::lean_dec(v_val_4317_);
                    leanh::lean_inc(v_declName_4299_);
                    v___x_4320_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0(v_declName_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
                    if leanh::lean_obj_tag(v___x_4320_) == 0 {
                        v_a_4321_ = leanh::lean_ctor_get(v___x_4320_, 0);
                        v_isSharedCheck_4376_ =
                            (!leanh::lean_is_exclusive(v___x_4320_)) as u8;
                        if v_isSharedCheck_4376_ == 0 {
                            v___x_4323_ = v___x_4320_;
                            v_isShared_4324_ = v_isSharedCheck_4376_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4321_);
                            leanh::lean_dec(v___x_4320_);
                            v___x_4323_ = leanh::lean_box(0);
                            v_isShared_4324_ = v_isSharedCheck_4376_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_4319_);
                        leanh::lean_dec(v_fst_4318_);
                        leanh::lean_dec(v_declName_4299_);
                        v_a_4377_ = leanh::lean_ctor_get(v___x_4320_, 0);
                        v_isSharedCheck_4384_ =
                            (!leanh::lean_is_exclusive(v___x_4320_)) as u8;
                        if v_isSharedCheck_4384_ == 0 {
                            v___x_4379_ = v___x_4320_;
                            v_isShared_4380_ = v_isSharedCheck_4384_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4377_);
                            leanh::lean_dec(v___x_4320_);
                            v___x_4379_ = leanh::lean_box(0);
                            v_isShared_4380_ = v_isSharedCheck_4384_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4313_);
                    leanh::lean_dec(v_declName_4299_);
                    v___x_4385_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4316_ == 0 {
                        leanh::lean_ctor_set(v___x_4315_, 0, v___x_4385_);
                        v___x_4387_ = v___x_4315_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4388_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
                        v___x_4387_ = v_reuseFailAlloc_4388_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4321_) == 1 {
                    v_val_4325_ = leanh::lean_ctor_get(v_a_4321_, 0);
                    v_isSharedCheck_4371_ = (!leanh::lean_is_exclusive(v_a_4321_)) as u8;
                    if v_isSharedCheck_4371_ == 0 {
                        v___x_4327_ = v_a_4321_;
                        v_isShared_4328_ = v_isSharedCheck_4371_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4325_);
                        leanh::lean_dec(v_a_4321_);
                        v___x_4327_ = leanh::lean_box(0);
                        v_isShared_4328_ = v_isSharedCheck_4371_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4321_);
                    leanh::lean_dec(v_snd_4319_);
                    leanh::lean_dec(v_fst_4318_);
                    leanh::lean_dec(v_declName_4299_);
                    v___x_4372_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4324_ == 0 {
                        leanh::lean_ctor_set(v___x_4323_, 0, v___x_4372_);
                        v___x_4374_ = v___x_4323_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4375_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4372_);
                        v___x_4374_ = v_reuseFailAlloc_4375_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v_doc_4329_ = leanh::lean_ctor_get(v_a_4300_, 0);
                v_originInfo_x3f_4330_ = leanh::lean_ctor_get(v_a_4300_, 2);
                v___x_4331_ = 0;
                if leanh::lean_obj_tag(v_originInfo_x3f_4330_) == 0 {
                    v___x_4357_ = leanh::lean_box(0);
                    v___y_4333_ = v___x_4357_;
                    state = 4;
                    continue;
                } else {
                    v_val_4358_ = leanh::lean_ctor_get(v_originInfo_x3f_4330_, 0);
                    v___x_4359_ = l_Lean_Elab_Info_range_x3f(v_val_4358_);
                    if leanh::lean_obj_tag(v___x_4359_) == 0 {
                        v___x_4360_ = leanh::lean_box(0);
                        v___y_4333_ = v___x_4360_;
                        state = 4;
                        continue;
                    } else {
                        v_val_4361_ = leanh::lean_ctor_get(v___x_4359_, 0);
                        v_isSharedCheck_4370_ =
                            (!leanh::lean_is_exclusive(v___x_4359_)) as u8;
                        if v_isSharedCheck_4370_ == 0 {
                            v___x_4363_ = v___x_4359_;
                            v_isShared_4364_ = v_isSharedCheck_4370_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4361_);
                            leanh::lean_dec(v___x_4359_);
                            v___x_4363_ = leanh::lean_box(0);
                            v_isShared_4364_ = v_isSharedCheck_4370_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v_range_4334_ = leanh::lean_ctor_get(v_val_4325_, 0);
                v_selectionRange_4335_ = leanh::lean_ctor_get(v_val_4325_, 1);
                v_isSharedCheck_4356_ = (!leanh::lean_is_exclusive(v_val_4325_)) as u8;
                if v_isSharedCheck_4356_ == 0 {
                    v___x_4337_ = v_val_4325_;
                    v_isShared_4338_ = v_isSharedCheck_4356_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_selectionRange_4335_);
                    leanh::lean_inc(v_range_4334_);
                    leanh::lean_dec(v_val_4325_);
                    v___x_4337_ = leanh::lean_box(0);
                    v_isShared_4338_ = v_isSharedCheck_4356_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4339_ = l_Lean_DeclarationRange_toLspRange(v_range_4334_);
                v___x_4340_ = l_Lean_DeclarationRange_toLspRange(v_selectionRange_4335_);
                v___x_4341_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4341_, 0, v___y_4333_);
                leanh::lean_ctor_set(v___x_4341_, 1, v_snd_4319_);
                leanh::lean_ctor_set(v___x_4341_, 2, v___x_4339_);
                leanh::lean_ctor_set(v___x_4341_, 3, v___x_4340_);
                v___x_4342_ = lean_erase_macro_scopes(v_declName_4299_);
                if v_isShared_4338_ == 0 {
                    leanh::lean_ctor_set(v___x_4337_, 1, v___x_4342_);
                    leanh::lean_ctor_set(v___x_4337_, 0, v_fst_4318_);
                    v___x_4344_ = v___x_4337_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4355_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_fst_4318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 1, v___x_4342_);
                    v___x_4344_ = v_reuseFailAlloc_4355_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4328_ == 0 {
                    leanh::lean_ctor_set(v___x_4327_, 0, v___x_4344_);
                    v___x_4346_ = v___x_4327_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4344_);
                    v___x_4346_ = v_reuseFailAlloc_4354_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4347_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_4347_, 0, v___x_4341_);
                leanh::lean_ctor_set(v___x_4347_, 1, v___x_4346_);
                leanh::lean_ctor_set_uint8(
                    v___x_4347_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4331_,
                );
                v___x_4348_ = leanh::lean_unsigned_to_nat(1);
                v___x_4349_ = lean_mk_empty_array_with_capacity(v___x_4348_);
                v___x_4350_ = lean_array_push(v___x_4349_, v___x_4347_);
                if v_isShared_4324_ == 0 {
                    leanh::lean_ctor_set(v___x_4323_, 0, v___x_4350_);
                    v___x_4352_ = v___x_4323_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4350_);
                    v___x_4352_ = v_reuseFailAlloc_4353_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4352_;
            }
            9 => {
                v_text_4365_ = leanh::lean_ctor_get(v_doc_4329_, 3);
                leanh::lean_inc_ref(v_text_4365_);
                v___x_4366_ = l_Lean_Syntax_Range_toLspRange(v_text_4365_, v_val_4361_);
                if v_isShared_4364_ == 0 {
                    leanh::lean_ctor_set(v___x_4363_, 0, v___x_4366_);
                    v___x_4368_ = v___x_4363_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4369_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4366_);
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
                    v_reuseFailAlloc_4383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
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
                    v_reuseFailAlloc_4396_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
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
    mut v_declName_4398_: *mut leanh::LeanObject,
    mut v_a_4399_: *mut leanh::LeanObject,
    mut v_a_4400_: *mut leanh::LeanObject,
    mut v_a_4401_: *mut leanh::LeanObject,
    mut v_a_4402_: *mut leanh::LeanObject,
    mut v_a_4403_: *mut leanh::LeanObject,
    mut v_a_4404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4405_ = l_Lean_Server_locationLinksFromDecl(
        v_declName_4398_,
        v_a_4399_,
        v_a_4400_,
        v_a_4401_,
        v_a_4402_,
        v_a_4403_,
    );
    leanh::lean_dec(v_a_4403_);
    leanh::lean_dec_ref(v_a_4402_);
    leanh::lean_dec(v_a_4401_);
    leanh::lean_dec_ref(v_a_4400_);
    leanh::lean_dec_ref(v_a_4399_);
    return v_res_4405_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(
    mut v_declName_4406_: *mut leanh::LeanObject,
    mut v___y_4407_: *mut leanh::LeanObject,
    mut v___y_4408_: *mut leanh::LeanObject,
    mut v___y_4409_: *mut leanh::LeanObject,
    mut v___y_4410_: *mut leanh::LeanObject,
    mut v___y_4411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4413_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___redArg(v_declName_4406_, v___y_4411_);
    return v___x_4413_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0___boxed(
    mut v_declName_4414_: *mut leanh::LeanObject,
    mut v___y_4415_: *mut leanh::LeanObject,
    mut v___y_4416_: *mut leanh::LeanObject,
    mut v___y_4417_: *mut leanh::LeanObject,
    mut v___y_4418_: *mut leanh::LeanObject,
    mut v___y_4419_: *mut leanh::LeanObject,
    mut v___y_4420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4421_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__0(v_declName_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
    leanh::lean_dec(v___y_4419_);
    leanh::lean_dec_ref(v___y_4418_);
    leanh::lean_dec(v___y_4417_);
    leanh::lean_dec_ref(v___y_4416_);
    leanh::lean_dec_ref(v___y_4415_);
    return v_res_4421_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(
    mut v_declName_4422_: *mut leanh::LeanObject,
    mut v___y_4423_: *mut leanh::LeanObject,
    mut v___y_4424_: *mut leanh::LeanObject,
    mut v___y_4425_: *mut leanh::LeanObject,
    mut v___y_4426_: *mut leanh::LeanObject,
    mut v___y_4427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4429_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___redArg(v_declName_4422_, v___y_4427_);
    return v___x_4429_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1___boxed(
    mut v_declName_4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
    mut v___y_4434_: *mut leanh::LeanObject,
    mut v___y_4435_: *mut leanh::LeanObject,
    mut v___y_4436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4437_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Server_locationLinksFromDecl_spec__0_spec__1(v_declName_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
    leanh::lean_dec(v___y_4435_);
    leanh::lean_dec_ref(v___y_4434_);
    leanh::lean_dec(v___y_4433_);
    leanh::lean_dec_ref(v___y_4432_);
    leanh::lean_dec_ref(v___y_4431_);
    return v_res_4437_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(
    mut v_id_4438_: *mut leanh::LeanObject,
    mut v_x_4439_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4439_) == 1 {
        let mut v_i_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_i_4440_ = leanh::lean_ctor_get(v_x_4439_, 0);
        v_expr_4441_ = leanh::lean_ctor_get(v_i_4440_, 3);
        if leanh::lean_obj_tag(v_expr_4441_) == 1 {
            let mut v_isBinder_4442_: u8 = 0;
            v_isBinder_4442_ = leanh::lean_ctor_get_uint8(
                v_i_4440_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            );
            if v_isBinder_4442_ == 1 {
                let mut v_fvarId_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4444_: u8 = 0;
                v_fvarId_4443_ = leanh::lean_ctor_get(v_expr_4441_, 0);
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
    mut v_id_4448_: *mut leanh::LeanObject,
    mut v_x_4449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4450_: u8 = 0;
    let mut v_r_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4450_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0(v_id_4448_, v_x_4449_);
    leanh::lean_dec_ref(v_x_4449_);
    leanh::lean_dec(v_id_4448_);
    v_r_4451_ = leanh::lean_box((v_res_4450_) as usize);
    return v_r_4451_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(
    mut v_id_4452_: *mut leanh::LeanObject,
    mut v_a_4453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_infoTree_x3f_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_infoTree_x3f_4455_ = leanh::lean_ctor_get(v_a_4453_, 1);
    if leanh::lean_obj_tag(v_infoTree_x3f_4455_) == 1 {
        let mut v_val_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4456_ = leanh::lean_ctor_get(v_infoTree_x3f_4455_, 0);
        v___f_4457_ = leanh::lean_alloc_closure(l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
        leanh::lean_closure_set(v___f_4457_, 0, v_id_4452_);
        leanh::lean_inc(v_val_4456_);
        v___x_4458_ = l_Lean_Elab_InfoTree_findInfo_x3f(v___f_4457_, v_val_4456_);
        v___x_4459_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4459_, 0, v___x_4458_);
        return v___x_4459_;
    } else {
        let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_id_4452_);
        v___x_4460_ = leanh::lean_box(0);
        v___x_4461_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4461_, 0, v___x_4460_);
        return v___x_4461_;
    }
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg___boxed(
    mut v_id_4462_: *mut leanh::LeanObject,
    mut v_a_4463_: *mut leanh::LeanObject,
    mut v_a_4464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4465_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(
            v_id_4462_, v_a_4463_,
        );
    leanh::lean_dec_ref(v_a_4463_);
    return v_res_4465_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(
    mut v_id_4466_: *mut leanh::LeanObject,
    mut v_a_4467_: *mut leanh::LeanObject,
    mut v_a_4468_: *mut leanh::LeanObject,
    mut v_a_4469_: *mut leanh::LeanObject,
    mut v_a_4470_: *mut leanh::LeanObject,
    mut v_a_4471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4473_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(
            v_id_4466_, v_a_4467_,
        );
    return v___x_4473_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___boxed(
    mut v_id_4474_: *mut leanh::LeanObject,
    mut v_a_4475_: *mut leanh::LeanObject,
    mut v_a_4476_: *mut leanh::LeanObject,
    mut v_a_4477_: *mut leanh::LeanObject,
    mut v_a_4478_: *mut leanh::LeanObject,
    mut v_a_4479_: *mut leanh::LeanObject,
    mut v_a_4480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4481_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f(
            v_id_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_,
        );
    leanh::lean_dec(v_a_4479_);
    leanh::lean_dec_ref(v_a_4478_);
    leanh::lean_dec(v_a_4477_);
    leanh::lean_dec_ref(v_a_4476_);
    leanh::lean_dec_ref(v_a_4475_);
    return v_res_4481_;
}
pub unsafe fn l_Lean_Server_locationLinksFromBinder___redArg(
    mut v_id_4482_: *mut leanh::LeanObject,
    mut v_a_4483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4489_: u8 = 0;
    let mut v_val_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_originInfo_x3f_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: u8 = 0;
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4485_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromBinder_binderInfo_x3f___redArg(v_id_4482_, v_a_4483_);
                v_a_4486_ = leanh::lean_ctor_get(v___x_4485_, 0);
                v_isSharedCheck_4531_ = (!leanh::lean_is_exclusive(v___x_4485_)) as u8;
                if v_isSharedCheck_4531_ == 0 {
                    v___x_4488_ = v___x_4485_;
                    v_isShared_4489_ = v_isSharedCheck_4531_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4486_);
                    leanh::lean_dec(v___x_4485_);
                    v___x_4488_ = leanh::lean_box(0);
                    v_isShared_4489_ = v_isSharedCheck_4531_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4486_) == 1 {
                    v_val_4490_ = leanh::lean_ctor_get(v_a_4486_, 0);
                    leanh::lean_inc(v_val_4490_);
                    leanh::lean_dec_ref_known(v_a_4486_, 1);
                    v___x_4491_ = l_Lean_Elab_Info_range_x3f(v_val_4490_);
                    leanh::lean_dec(v_val_4490_);
                    if leanh::lean_obj_tag(v___x_4491_) == 1 {
                        v_doc_4492_ = leanh::lean_ctor_get(v_a_4483_, 0);
                        v_val_4493_ = leanh::lean_ctor_get(v___x_4491_, 0);
                        leanh::lean_inc(v_val_4493_);
                        leanh::lean_dec_ref_known(v___x_4491_, 1);
                        v_originInfo_x3f_4494_ = leanh::lean_ctor_get(v_a_4483_, 2);
                        v_uri_4495_ = leanh::lean_ctor_get(v_doc_4492_, 0);
                        v_text_4496_ = leanh::lean_ctor_get(v_doc_4492_, 3);
                        leanh::lean_inc_ref(v_text_4496_);
                        v___x_4497_ = l_Lean_Syntax_Range_toLspRange(v_text_4496_, v_val_4493_);
                        if leanh::lean_obj_tag(v_originInfo_x3f_4494_) == 0 {
                            v___x_4510_ = leanh::lean_box(0);
                            v___y_4499_ = v___x_4510_;
                            state = 2;
                            continue;
                        } else {
                            v_val_4511_ = leanh::lean_ctor_get(v_originInfo_x3f_4494_, 0);
                            v___x_4512_ = l_Lean_Elab_Info_range_x3f(v_val_4511_);
                            if leanh::lean_obj_tag(v___x_4512_) == 0 {
                                v___x_4513_ = leanh::lean_box(0);
                                v___y_4499_ = v___x_4513_;
                                state = 2;
                                continue;
                            } else {
                                v_val_4514_ = leanh::lean_ctor_get(v___x_4512_, 0);
                                v_isSharedCheck_4522_ =
                                    (!leanh::lean_is_exclusive(v___x_4512_)) as u8;
                                if v_isSharedCheck_4522_ == 0 {
                                    v___x_4516_ = v___x_4512_;
                                    v_isShared_4517_ = v_isSharedCheck_4522_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_4514_);
                                    leanh::lean_dec(v___x_4512_);
                                    v___x_4516_ = leanh::lean_box(0);
                                    v_isShared_4517_ = v_isSharedCheck_4522_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_4491_);
                        v___x_4523_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        if v_isShared_4489_ == 0 {
                            leanh::lean_ctor_set(v___x_4488_, 0, v___x_4523_);
                            v___x_4525_ = v___x_4488_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4526_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4523_);
                            v___x_4525_ = v_reuseFailAlloc_4526_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4486_);
                    v___x_4527_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4489_ == 0 {
                        leanh::lean_ctor_set(v___x_4488_, 0, v___x_4527_);
                        v___x_4529_ = v___x_4488_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4530_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4527_);
                        v___x_4529_ = v_reuseFailAlloc_4530_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_4497_);
                leanh::lean_inc_ref(v_uri_4495_);
                v___x_4500_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4500_, 0, v___y_4499_);
                leanh::lean_ctor_set(v___x_4500_, 1, v_uri_4495_);
                leanh::lean_ctor_set(v___x_4500_, 2, v___x_4497_);
                leanh::lean_ctor_set(v___x_4500_, 3, v___x_4497_);
                v___x_4501_ = leanh::lean_box(0);
                v___x_4502_ = 0;
                v___x_4503_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_4503_, 0, v___x_4500_);
                leanh::lean_ctor_set(v___x_4503_, 1, v___x_4501_);
                leanh::lean_ctor_set_uint8(
                    v___x_4503_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4502_,
                );
                v___x_4504_ = leanh::lean_unsigned_to_nat(1);
                v___x_4505_ = lean_mk_empty_array_with_capacity(v___x_4504_);
                v___x_4506_ = lean_array_push(v___x_4505_, v___x_4503_);
                if v_isShared_4489_ == 0 {
                    leanh::lean_ctor_set(v___x_4488_, 0, v___x_4506_);
                    v___x_4508_ = v___x_4488_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
                    v___x_4508_ = v_reuseFailAlloc_4509_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4508_;
            }
            4 => {
                leanh::lean_inc_ref(v_text_4496_);
                v___x_4518_ = l_Lean_Syntax_Range_toLspRange(v_text_4496_, v_val_4514_);
                if v_isShared_4517_ == 0 {
                    leanh::lean_ctor_set(v___x_4516_, 0, v___x_4518_);
                    v___x_4520_ = v___x_4516_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
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
    mut v_id_4532_: *mut leanh::LeanObject,
    mut v_a_4533_: *mut leanh::LeanObject,
    mut v_a_4534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4535_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_4532_, v_a_4533_);
    leanh::lean_dec_ref(v_a_4533_);
    return v_res_4535_;
}
pub unsafe fn l_Lean_Server_locationLinksFromBinder(
    mut v_id_4536_: *mut leanh::LeanObject,
    mut v_a_4537_: *mut leanh::LeanObject,
    mut v_a_4538_: *mut leanh::LeanObject,
    mut v_a_4539_: *mut leanh::LeanObject,
    mut v_a_4540_: *mut leanh::LeanObject,
    mut v_a_4541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4543_ = l_Lean_Server_locationLinksFromBinder___redArg(v_id_4536_, v_a_4537_);
    return v___x_4543_;
}
pub unsafe fn l_Lean_Server_locationLinksFromBinder___boxed(
    mut v_id_4544_: *mut leanh::LeanObject,
    mut v_a_4545_: *mut leanh::LeanObject,
    mut v_a_4546_: *mut leanh::LeanObject,
    mut v_a_4547_: *mut leanh::LeanObject,
    mut v_a_4548_: *mut leanh::LeanObject,
    mut v_a_4549_: *mut leanh::LeanObject,
    mut v_a_4550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4551_ = l_Lean_Server_locationLinksFromBinder(
        v_id_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_,
    );
    leanh::lean_dec(v_a_4549_);
    leanh::lean_dec_ref(v_a_4548_);
    leanh::lean_dec(v_a_4547_);
    leanh::lean_dec_ref(v_a_4546_);
    leanh::lean_dec_ref(v_a_4545_);
    return v_res_4551_;
}
pub unsafe fn l_Lean_Server_locationLinksFromImport___redArg(
    mut v_i_4583_: *mut leanh::LeanObject,
    mut v_a_4584_: *mut leanh::LeanObject,
    mut v_a_4585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: u8 = 0;
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: u8 = 0;
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v_val_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v_text_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4637_: u8 = 0;
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut v_a_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4646_: u8 = 0;
    let mut v_ref_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut v___y_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: u8 = 0;
    let mut v___x_4664_: u8 = 0;
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: u8 = 0;
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: u8 = 0;
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: u8 = 0;
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: u8 = 0;
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: u8 = 0;
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4696_: u8 = 0;
    let mut v_unused_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stx_4599_ = leanh::lean_ctor_get(v_i_4583_, 1);
                v_isSharedCheck_4696_ = (!leanh::lean_is_exclusive(v_i_4583_)) as u8;
                if v_isSharedCheck_4696_ == 0 {
                    v_unused_4697_ = leanh::lean_ctor_get(v_i_4583_, 0);
                    leanh::lean_dec(v_unused_4697_);
                    v___x_4601_ = v_i_4583_;
                    v_isShared_4602_ = v_isSharedCheck_4696_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_stx_4599_);
                    leanh::lean_dec(v_i_4583_);
                    v___x_4601_ = leanh::lean_box(0);
                    v_isShared_4602_ = v_isSharedCheck_4696_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v___y_4588_, 2);
                v___x_4591_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4591_, 0, v___y_4590_);
                leanh::lean_ctor_set(v___x_4591_, 1, v___y_4589_);
                leanh::lean_ctor_set(v___x_4591_, 2, v___y_4588_);
                leanh::lean_ctor_set(v___x_4591_, 3, v___y_4588_);
                v___x_4592_ = leanh::lean_box(0);
                v___x_4593_ = 0;
                v___x_4594_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_4594_, 0, v___x_4591_);
                leanh::lean_ctor_set(v___x_4594_, 1, v___x_4592_);
                leanh::lean_ctor_set_uint8(
                    v___x_4594_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4593_,
                );
                v___x_4595_ = leanh::lean_unsigned_to_nat(1);
                v___x_4596_ = lean_mk_empty_array_with_capacity(v___x_4595_);
                v___x_4597_ = lean_array_push(v___x_4596_, v___x_4594_);
                v___x_4598_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4598_, 0, v___x_4597_);
                return v___x_4598_;
            }
            2 => {
                v___x_4603_ = l_Lean_Server_locationLinksFromImport___redArg___closed__4;
                leanh::lean_inc(v_stx_4599_);
                v___x_4604_ = l_Lean_Syntax_isOfKind(v_stx_4599_, v___x_4603_);
                if v___x_4604_ == 0 {
                    leanh::lean_del_object(v___x_4601_);
                    leanh::lean_dec(v_stx_4599_);
                    v___x_4605_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v___x_4606_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4606_, 0, v___x_4605_);
                    return v___x_4606_;
                } else {
                    v___x_4607_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4685_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4607_);
                    v___x_4686_ = l_Lean_Syntax_isNone(v___x_4685_);
                    if v___x_4686_ == 0 {
                        v___x_4687_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_4685_);
                        v___x_4688_ = l_Lean_Syntax_matchesNull(v___x_4685_, v___x_4687_);
                        if v___x_4688_ == 0 {
                            leanh::lean_dec(v___x_4685_);
                            leanh::lean_del_object(v___x_4601_);
                            leanh::lean_dec(v_stx_4599_);
                            v___x_4689_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                            v___x_4690_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4690_, 0, v___x_4689_);
                            return v___x_4690_;
                        } else {
                            v___x_4691_ = l_Lean_Syntax_getArg(v___x_4685_, v___x_4607_);
                            leanh::lean_dec(v___x_4685_);
                            v___x_4692_ =
                                l_Lean_Server_locationLinksFromImport___redArg___closed__12;
                            v___x_4693_ = l_Lean_Syntax_isOfKind(v___x_4691_, v___x_4692_);
                            if v___x_4693_ == 0 {
                                leanh::lean_del_object(v___x_4601_);
                                leanh::lean_dec(v_stx_4599_);
                                v___x_4694_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                                v___x_4695_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4695_, 0, v___x_4694_);
                                return v___x_4695_;
                            } else {
                                v___y_4673_ = v_a_4585_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_4685_);
                        v___y_4673_ = v_a_4585_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4610_ = leanh::lean_unsigned_to_nat(5);
                v___x_4611_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4610_);
                v___x_4612_ = l_Lean_Syntax_matchesNull(v___x_4611_, v___x_4607_);
                if v___x_4612_ == 0 {
                    leanh::lean_del_object(v___x_4601_);
                    leanh::lean_dec(v_stx_4599_);
                    v___x_4613_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v___x_4614_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4614_, 0, v___x_4613_);
                    return v___x_4614_;
                } else {
                    v___x_4615_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4616_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4615_);
                    leanh::lean_dec(v_stx_4599_);
                    v___x_4617_ = l_Lean_TSyntax_getId(v___x_4616_);
                    v___x_4618_ = l_Lean_Server_documentUriFromModule_x3f(v___x_4617_);
                    if leanh::lean_obj_tag(v___x_4618_) == 0 {
                        leanh::lean_del_object(v___x_4601_);
                        v_a_4619_ = leanh::lean_ctor_get(v___x_4618_, 0);
                        v_isSharedCheck_4642_ =
                            (!leanh::lean_is_exclusive(v___x_4618_)) as u8;
                        if v_isSharedCheck_4642_ == 0 {
                            v___x_4621_ = v___x_4618_;
                            v_isShared_4622_ = v_isSharedCheck_4642_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4619_);
                            leanh::lean_dec(v___x_4618_);
                            v___x_4621_ = leanh::lean_box(0);
                            v_isShared_4622_ = v_isSharedCheck_4642_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4616_);
                        v_a_4643_ = leanh::lean_ctor_get(v___x_4618_, 0);
                        v_isSharedCheck_4657_ =
                            (!leanh::lean_is_exclusive(v___x_4618_)) as u8;
                        if v_isSharedCheck_4657_ == 0 {
                            v___x_4645_ = v___x_4618_;
                            v_isShared_4646_ = v_isSharedCheck_4657_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4643_);
                            leanh::lean_dec(v___x_4618_);
                            v___x_4645_ = leanh::lean_box(0);
                            v_isShared_4646_ = v_isSharedCheck_4657_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if leanh::lean_obj_tag(v_a_4619_) == 1 {
                    leanh::lean_del_object(v___x_4621_);
                    v_val_4623_ = leanh::lean_ctor_get(v_a_4619_, 0);
                    leanh::lean_inc(v_val_4623_);
                    leanh::lean_dec_ref_known(v_a_4619_, 1);
                    v___x_4624_ = l_Lean_Server_locationLinksFromImport___redArg___closed__6;
                    v___x_4625_ = l_Lean_Syntax_getRange_x3f(v___x_4616_, v___x_4604_);
                    leanh::lean_dec(v___x_4616_);
                    if leanh::lean_obj_tag(v___x_4625_) == 0 {
                        v___x_4626_ = leanh::lean_box(0);
                        v___y_4588_ = v___x_4624_;
                        v___y_4589_ = v_val_4623_;
                        v___y_4590_ = v___x_4626_;
                        state = 1;
                        continue;
                    } else {
                        v_doc_4627_ = leanh::lean_ctor_get(v_a_4584_, 0);
                        v_val_4628_ = leanh::lean_ctor_get(v___x_4625_, 0);
                        v_isSharedCheck_4637_ =
                            (!leanh::lean_is_exclusive(v___x_4625_)) as u8;
                        if v_isSharedCheck_4637_ == 0 {
                            v___x_4630_ = v___x_4625_;
                            v_isShared_4631_ = v_isSharedCheck_4637_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4628_);
                            leanh::lean_dec(v___x_4625_);
                            v___x_4630_ = leanh::lean_box(0);
                            v_isShared_4631_ = v_isSharedCheck_4637_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4619_);
                    leanh::lean_dec(v___x_4616_);
                    v___x_4638_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4622_ == 0 {
                        leanh::lean_ctor_set(v___x_4621_, 0, v___x_4638_);
                        v___x_4640_ = v___x_4621_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4641_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
                        v___x_4640_ = v_reuseFailAlloc_4641_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v_text_4632_ = leanh::lean_ctor_get(v_doc_4627_, 3);
                leanh::lean_inc_ref(v_text_4632_);
                v___x_4633_ = l_Lean_Syntax_Range_toLspRange(v_text_4632_, v_val_4628_);
                if v_isShared_4631_ == 0 {
                    leanh::lean_ctor_set(v___x_4630_, 0, v___x_4633_);
                    v___x_4635_ = v___x_4630_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4636_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
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
                v_ref_4647_ = leanh::lean_ctor_get(v___y_4609_, 5);
                v___x_4648_ = lean_io_error_to_string(v_a_4643_);
                v___x_4649_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4649_, 0, v___x_4648_);
                v___x_4650_ = l_Lean_MessageData_ofFormat(v___x_4649_);
                leanh::lean_inc(v_ref_4647_);
                if v_isShared_4602_ == 0 {
                    leanh::lean_ctor_set(v___x_4601_, 1, v___x_4650_);
                    leanh::lean_ctor_set(v___x_4601_, 0, v_ref_4647_);
                    v___x_4652_ = v___x_4601_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4656_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_ref_4647_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 1, v___x_4650_);
                    v___x_4652_ = v_reuseFailAlloc_4656_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4646_ == 0 {
                    leanh::lean_ctor_set(v___x_4645_, 0, v___x_4652_);
                    v___x_4654_ = v___x_4645_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
                    v___x_4654_ = v_reuseFailAlloc_4655_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4654_;
            }
            11 => {
                v___x_4661_ = leanh::lean_unsigned_to_nat(3);
                v___x_4662_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4661_);
                v___x_4663_ = l_Lean_Syntax_isNone(v___x_4662_);
                if v___x_4663_ == 0 {
                    leanh::lean_inc(v___x_4662_);
                    v___x_4664_ = l_Lean_Syntax_matchesNull(v___x_4662_, v___y_4659_);
                    if v___x_4664_ == 0 {
                        leanh::lean_dec(v___x_4662_);
                        leanh::lean_del_object(v___x_4601_);
                        leanh::lean_dec(v_stx_4599_);
                        v___x_4665_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        v___x_4666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4666_, 0, v___x_4665_);
                        return v___x_4666_;
                    } else {
                        v___x_4667_ = l_Lean_Syntax_getArg(v___x_4662_, v___x_4607_);
                        leanh::lean_dec(v___x_4662_);
                        v___x_4668_ = l_Lean_Server_locationLinksFromImport___redArg___closed__8;
                        v___x_4669_ = l_Lean_Syntax_isOfKind(v___x_4667_, v___x_4668_);
                        if v___x_4669_ == 0 {
                            leanh::lean_del_object(v___x_4601_);
                            leanh::lean_dec(v_stx_4599_);
                            v___x_4670_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                            v___x_4671_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4671_, 0, v___x_4670_);
                            return v___x_4671_;
                        } else {
                            v___y_4609_ = v___y_4660_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4662_);
                    v___y_4609_ = v___y_4660_;
                    state = 3;
                    continue;
                }
            }
            12 => {
                v___x_4674_ = leanh::lean_unsigned_to_nat(1);
                v___x_4675_ = l_Lean_Syntax_getArg(v_stx_4599_, v___x_4674_);
                v___x_4676_ = l_Lean_Syntax_isNone(v___x_4675_);
                if v___x_4676_ == 0 {
                    leanh::lean_inc(v___x_4675_);
                    v___x_4677_ = l_Lean_Syntax_matchesNull(v___x_4675_, v___x_4674_);
                    if v___x_4677_ == 0 {
                        leanh::lean_dec(v___x_4675_);
                        leanh::lean_del_object(v___x_4601_);
                        leanh::lean_dec(v_stx_4599_);
                        v___x_4678_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        v___x_4679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4679_, 0, v___x_4678_);
                        return v___x_4679_;
                    } else {
                        v___x_4680_ = l_Lean_Syntax_getArg(v___x_4675_, v___x_4607_);
                        leanh::lean_dec(v___x_4675_);
                        v___x_4681_ = l_Lean_Server_locationLinksFromImport___redArg___closed__10;
                        v___x_4682_ = l_Lean_Syntax_isOfKind(v___x_4680_, v___x_4681_);
                        if v___x_4682_ == 0 {
                            leanh::lean_del_object(v___x_4601_);
                            leanh::lean_dec(v_stx_4599_);
                            v___x_4683_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                            v___x_4684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4684_, 0, v___x_4683_);
                            return v___x_4684_;
                        } else {
                            v___y_4659_ = v___x_4674_;
                            v___y_4660_ = v___y_4673_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4675_);
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
    mut v_i_4698_: *mut leanh::LeanObject,
    mut v_a_4699_: *mut leanh::LeanObject,
    mut v_a_4700_: *mut leanh::LeanObject,
    mut v_a_4701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4702_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_4698_, v_a_4699_, v_a_4700_);
    leanh::lean_dec_ref(v_a_4700_);
    leanh::lean_dec_ref(v_a_4699_);
    return v_res_4702_;
}
pub unsafe fn l_Lean_Server_locationLinksFromImport(
    mut v_i_4703_: *mut leanh::LeanObject,
    mut v_a_4704_: *mut leanh::LeanObject,
    mut v_a_4705_: *mut leanh::LeanObject,
    mut v_a_4706_: *mut leanh::LeanObject,
    mut v_a_4707_: *mut leanh::LeanObject,
    mut v_a_4708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4710_ = l_Lean_Server_locationLinksFromImport___redArg(v_i_4703_, v_a_4704_, v_a_4707_);
    return v___x_4710_;
}
pub unsafe fn l_Lean_Server_locationLinksFromImport___boxed(
    mut v_i_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
    mut v_a_4713_: *mut leanh::LeanObject,
    mut v_a_4714_: *mut leanh::LeanObject,
    mut v_a_4715_: *mut leanh::LeanObject,
    mut v_a_4716_: *mut leanh::LeanObject,
    mut v_a_4717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4718_ = l_Lean_Server_locationLinksFromImport(
        v_i_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_,
    );
    leanh::lean_dec(v_a_4716_);
    leanh::lean_dec_ref(v_a_4715_);
    leanh::lean_dec(v_a_4714_);
    leanh::lean_dec_ref(v_a_4713_);
    leanh::lean_dec_ref(v_a_4712_);
    return v_res_4718_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(
    mut v_a_4738_: *mut leanh::LeanObject,
    mut v_a_4739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_originInfo_x3f_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4746_: u8 = 0;
    let mut v_val_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4752_: u8 = 0;
    let mut v_elaborator_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4757_: u8 = 0;
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: u8 = 0;
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: u8 = 0;
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: u8 = 0;
    let mut v_env_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: u8 = 0;
    let mut v_names_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: u8 = 0;
    let mut v___x_4777_: u8 = 0;
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: u8 = 0;
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4785_: u8 = 0;
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4741_ = lean_st_ref_get(v_a_4739_);
                v_originInfo_x3f_4745_ = leanh::lean_ctor_get(v_a_4738_, 2);
                if leanh::lean_obj_tag(v_originInfo_x3f_4745_) == 1 {
                    v_kind_4746_ = leanh::lean_ctor_get_uint8(
                        v_a_4738_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v_val_4747_ = leanh::lean_ctor_get(v_originInfo_x3f_4745_, 0);
                    leanh::lean_inc(v_val_4747_);
                    v___x_4748_ = l_Lean_Elab_Info_toElabInfo_x3f(v_val_4747_);
                    if leanh::lean_obj_tag(v___x_4748_) == 1 {
                        v_val_4749_ = leanh::lean_ctor_get(v___x_4748_, 0);
                        v_isSharedCheck_4785_ =
                            (!leanh::lean_is_exclusive(v___x_4748_)) as u8;
                        if v_isSharedCheck_4785_ == 0 {
                            v___x_4751_ = v___x_4748_;
                            v_isShared_4752_ = v_isSharedCheck_4785_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4749_);
                            leanh::lean_dec(v___x_4748_);
                            v___x_4751_ = leanh::lean_box(0);
                            v_isShared_4752_ = v_isSharedCheck_4785_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4748_);
                        leanh::lean_dec(v___x_4741_);
                        v___x_4786_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                        v___x_4787_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4787_, 0, v___x_4786_);
                        return v___x_4787_;
                    }
                } else {
                    leanh::lean_dec(v___x_4741_);
                    v___x_4788_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                    v___x_4789_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4789_, 0, v___x_4788_);
                    return v___x_4789_;
                }
            }
            1 => {
                v___x_4743_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                v___x_4744_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4744_, 0, v___x_4743_);
                return v___x_4744_;
            }
            2 => {
                v_elaborator_4753_ = leanh::lean_ctor_get(v_val_4749_, 0);
                leanh::lean_inc(v_elaborator_4753_);
                v_stx_4754_ = leanh::lean_ctor_get(v_val_4749_, 1);
                leanh::lean_inc(v_stx_4754_);
                leanh::lean_dec(v_val_4749_);
                v___x_4766_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__2;
                v___x_4767_ = lean_name_eq(v_elaborator_4753_, v___x_4766_);
                if v___x_4767_ == 0 {
                    v___x_4768_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__6;
                    v___x_4769_ = lean_name_eq(v_elaborator_4753_, v___x_4768_);
                    if v___x_4769_ == 0 {
                        v___x_4770_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__8;
                        v___x_4771_ = lean_name_eq(v_elaborator_4753_, v___x_4770_);
                        if v___x_4771_ == 0 {
                            v_env_4772_ = leanh::lean_ctor_get(v___x_4741_, 0);
                            leanh::lean_inc_ref_n(v_env_4772_, 2);
                            leanh::lean_dec(v___x_4741_);
                            v___x_4773_ = 1;
                            v___x_4780_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                            leanh::lean_inc(v_elaborator_4753_);
                            v___x_4781_ = l_Lean_Environment_contains(
                                v_env_4772_,
                                v_elaborator_4753_,
                                v___x_4773_,
                            );
                            if v___x_4781_ == 0 {
                                leanh::lean_dec(v_elaborator_4753_);
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
                            leanh::lean_dec(v_stx_4754_);
                            leanh::lean_dec(v_elaborator_4753_);
                            leanh::lean_del_object(v___x_4751_);
                            leanh::lean_dec(v___x_4741_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_stx_4754_);
                        leanh::lean_dec(v_elaborator_4753_);
                        leanh::lean_del_object(v___x_4751_);
                        leanh::lean_dec(v___x_4741_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_stx_4754_);
                    leanh::lean_dec(v_elaborator_4753_);
                    leanh::lean_del_object(v___x_4751_);
                    leanh::lean_dec(v___x_4741_);
                    v___x_4783_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                    v___x_4784_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4784_, 0, v___x_4783_);
                    return v___x_4784_;
                }
            }
            3 => {
                if v___y_4757_ == 0 {
                    leanh::lean_dec(v_stx_4754_);
                    if v_isShared_4752_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4751_, 0);
                        leanh::lean_ctor_set(v___x_4751_, 0, v___y_4756_);
                        v___x_4759_ = v___x_4751_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4760_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___y_4756_);
                        v___x_4759_ = v_reuseFailAlloc_4760_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_4761_ = l_Lean_Syntax_getKind(v_stx_4754_);
                    v___x_4762_ = lean_array_push(v___y_4756_, v___x_4761_);
                    if v_isShared_4752_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4751_, 0);
                        leanh::lean_ctor_set(v___x_4751_, 0, v___x_4762_);
                        v___x_4764_ = v___x_4751_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
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
                    leanh::lean_dec_ref(v_env_4772_);
                    v___y_4756_ = v_names_4775_;
                    v___y_4757_ = v___x_4777_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_stx_4754_);
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
    mut v_a_4790_: *mut leanh::LeanObject,
    mut v_a_4791_: *mut leanh::LeanObject,
    mut v_a_4792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4793_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(
            v_a_4790_, v_a_4791_,
        );
    leanh::lean_dec(v_a_4791_);
    leanh::lean_dec_ref(v_a_4790_);
    return v_res_4793_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(
    mut v_a_4794_: *mut leanh::LeanObject,
    mut v_a_4795_: *mut leanh::LeanObject,
    mut v_a_4796_: *mut leanh::LeanObject,
    mut v_a_4797_: *mut leanh::LeanObject,
    mut v_a_4798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ =
        l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(
            v_a_4794_, v_a_4798_,
        );
    return v___x_4800_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___boxed(
    mut v_a_4801_: *mut leanh::LeanObject,
    mut v_a_4802_: *mut leanh::LeanObject,
    mut v_a_4803_: *mut leanh::LeanObject,
    mut v_a_4804_: *mut leanh::LeanObject,
    mut v_a_4805_: *mut leanh::LeanObject,
    mut v_a_4806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4807_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames(
        v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_,
    );
    leanh::lean_dec(v_a_4805_);
    leanh::lean_dec_ref(v_a_4804_);
    leanh::lean_dec(v_a_4803_);
    leanh::lean_dec_ref(v_a_4802_);
    leanh::lean_dec_ref(v_a_4801_);
    return v_res_4807_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(
    mut v_as_4808_: *mut leanh::LeanObject,
    mut v_sz_4809_: usize,
    mut v_i_4810_: usize,
    mut v_b_4811_: *mut leanh::LeanObject,
    mut v___y_4812_: *mut leanh::LeanObject,
    mut v___y_4813_: *mut leanh::LeanObject,
    mut v___y_4814_: *mut leanh::LeanObject,
    mut v___y_4815_: *mut leanh::LeanObject,
    mut v___y_4816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4818_: u8 = 0;
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: usize = 0;
    let mut v___x_4825_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4818_ = lean_usize_dec_lt(v_i_4810_, v_sz_4809_);
                if v___x_4818_ == 0 {
                    v___x_4819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4819_, 0, v_b_4811_);
                    return v___x_4819_;
                } else {
                    v_a_4820_ = lean_array_uget_borrowed(v_as_4808_, v_i_4810_);
                    leanh::lean_inc(v_a_4820_);
                    v___x_4821_ = l_Lean_Server_locationLinksFromDecl(
                        v_a_4820_,
                        v___y_4812_,
                        v___y_4813_,
                        v___y_4814_,
                        v___y_4815_,
                        v___y_4816_,
                    );
                    if leanh::lean_obj_tag(v___x_4821_) == 0 {
                        v_a_4822_ = leanh::lean_ctor_get(v___x_4821_, 0);
                        leanh::lean_inc(v_a_4822_);
                        leanh::lean_dec_ref_known(v___x_4821_, 1);
                        v___x_4823_ = l_Array_append___redArg(v_b_4811_, v_a_4822_);
                        leanh::lean_dec(v_a_4822_);
                        v___x_4824_ = 1usize;
                        v___x_4825_ = lean_usize_add(v_i_4810_, v___x_4824_);
                        v_i_4810_ = v___x_4825_;
                        v_b_4811_ = v___x_4823_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_4811_);
                        return v___x_4821_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0___boxed(
    mut v_as_4827_: *mut leanh::LeanObject,
    mut v_sz_4828_: *mut leanh::LeanObject,
    mut v_i_4829_: *mut leanh::LeanObject,
    mut v_b_4830_: *mut leanh::LeanObject,
    mut v___y_4831_: *mut leanh::LeanObject,
    mut v___y_4832_: *mut leanh::LeanObject,
    mut v___y_4833_: *mut leanh::LeanObject,
    mut v___y_4834_: *mut leanh::LeanObject,
    mut v___y_4835_: *mut leanh::LeanObject,
    mut v___y_4836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4837_: usize = 0;
    let mut v_i_boxed_4838_: usize = 0;
    let mut v_res_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4837_ = leanh::lean_unbox_usize(v_sz_4828_);
    leanh::lean_dec(v_sz_4828_);
    v_i_boxed_4838_ = leanh::lean_unbox_usize(v_i_4829_);
    leanh::lean_dec(v_i_4829_);
    v_res_4839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_as_4827_, v_sz_boxed_4837_, v_i_boxed_4838_, v_b_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
    leanh::lean_dec(v___y_4835_);
    leanh::lean_dec_ref(v___y_4834_);
    leanh::lean_dec(v___y_4833_);
    leanh::lean_dec_ref(v___y_4832_);
    leanh::lean_dec_ref(v___y_4831_);
    leanh::lean_dec_ref(v_as_4827_);
    return v_res_4839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(
    mut v_sz_4840_: usize,
    mut v_i_4841_: usize,
    mut v_bs_4842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4843_: u8 = 0;
    let mut v_v_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLocationLink_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ident_x3f_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4849_: u8 = 0;
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: usize = 0;
    let mut v___x_4855_: usize = 0;
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    v_toLocationLink_4845_ = leanh::lean_ctor_get(v_v_4844_, 0);
                    v_ident_x3f_4846_ = leanh::lean_ctor_get(v_v_4844_, 1);
                    v_isSharedCheck_4859_ = (!leanh::lean_is_exclusive(v_v_4844_)) as u8;
                    if v_isSharedCheck_4859_ == 0 {
                        v___x_4848_ = v_v_4844_;
                        v_isShared_4849_ = v_isSharedCheck_4859_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_ident_x3f_4846_);
                        leanh::lean_inc(v_toLocationLink_4845_);
                        leanh::lean_dec(v_v_4844_);
                        v___x_4848_ = leanh::lean_box(0);
                        v_isShared_4849_ = v_isSharedCheck_4859_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4850_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_4851_ = lean_array_uset(v_bs_4842_, v_i_4841_, v___x_4850_);
                if v_isShared_4849_ == 0 {
                    v___x_4853_ = v___x_4848_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_toLocationLink_4845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_ident_x3f_4846_);
                    v___x_4853_ = v_reuseFailAlloc_4858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4853_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_sz_4860_: *mut leanh::LeanObject,
    mut v_i_4861_: *mut leanh::LeanObject,
    mut v_bs_4862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4863_: usize = 0;
    let mut v_i_boxed_4864_: usize = 0;
    let mut v_res_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4863_ = leanh::lean_unbox_usize(v_sz_4860_);
    leanh::lean_dec(v_sz_4860_);
    v_i_boxed_4864_ = leanh::lean_unbox_usize(v_i_4861_);
    leanh::lean_dec(v_i_4861_);
    v_res_4865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_locationLinksDefault_spec__1(v_sz_boxed_4863_, v_i_boxed_4864_, v_bs_4862_);
    return v_res_4865_;
}
pub unsafe fn l_Lean_Server_locationLinksDefault(
    mut v_a_4866_: *mut leanh::LeanObject,
    mut v_a_4867_: *mut leanh::LeanObject,
    mut v_a_4868_: *mut leanh::LeanObject,
    mut v_a_4869_: *mut leanh::LeanObject,
    mut v_a_4870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4875_: usize = 0;
    let mut v___x_4876_: usize = 0;
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v_sz_4882_: usize = 0;
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4872_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg(v_a_4866_, v_a_4870_);
                v_a_4873_ = leanh::lean_ctor_get(v___x_4872_, 0);
                leanh::lean_inc(v_a_4873_);
                leanh::lean_dec_ref(v___x_4872_);
                v___x_4874_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                v_sz_4875_ = lean_array_size(v_a_4873_);
                v___x_4876_ = 0usize;
                v___x_4877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_4873_, v_sz_4875_, v___x_4876_, v___x_4874_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
                leanh::lean_dec(v_a_4873_);
                if leanh::lean_obj_tag(v___x_4877_) == 0 {
                    v_a_4878_ = leanh::lean_ctor_get(v___x_4877_, 0);
                    v_isSharedCheck_4887_ = (!leanh::lean_is_exclusive(v___x_4877_)) as u8;
                    if v_isSharedCheck_4887_ == 0 {
                        v___x_4880_ = v___x_4877_;
                        v_isShared_4881_ = v_isSharedCheck_4887_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4878_);
                        leanh::lean_dec(v___x_4877_);
                        v___x_4880_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_4883_);
                    v___x_4885_ = v___x_4880_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
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
    mut v_a_4888_: *mut leanh::LeanObject,
    mut v_a_4889_: *mut leanh::LeanObject,
    mut v_a_4890_: *mut leanh::LeanObject,
    mut v_a_4891_: *mut leanh::LeanObject,
    mut v_a_4892_: *mut leanh::LeanObject,
    mut v_a_4893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4894_ =
        l_Lean_Server_locationLinksDefault(v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_);
    leanh::lean_dec(v_a_4892_);
    leanh::lean_dec_ref(v_a_4891_);
    leanh::lean_dec(v_a_4890_);
    leanh::lean_dec_ref(v_a_4889_);
    leanh::lean_dec_ref(v_a_4888_);
    return v_res_4894_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(
    mut v_name_4895_: *mut leanh::LeanObject,
    mut v___y_4896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4898_ = lean_st_ref_get(v___y_4896_);
    v_env_4899_ = leanh::lean_ctor_get(v___x_4898_, 0);
    leanh::lean_inc_ref(v_env_4899_);
    leanh::lean_dec(v___x_4898_);
    v___x_4900_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_4901_ = leanh::lean_ctor_get(v___x_4900_, 0);
    v_asyncMode_4902_ = leanh::lean_ctor_get(v_toEnvExtension_4901_, 2);
    v___x_4903_ = leanh::lean_box(1);
    v___x_4904_ = leanh::lean_box(0);
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
    leanh::lean_dec(v___x_4905_);
    v___x_4907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4907_, 0, v___x_4906_);
    return v___x_4907_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg___boxed(
    mut v_name_4908_: *mut leanh::LeanObject,
    mut v___y_4909_: *mut leanh::LeanObject,
    mut v___y_4910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4911_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_4908_, v___y_4909_);
    leanh::lean_dec(v___y_4909_);
    leanh::lean_dec(v_name_4908_);
    return v_res_4911_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(
    mut v_name_4912_: *mut leanh::LeanObject,
    mut v___y_4913_: *mut leanh::LeanObject,
    mut v___y_4914_: *mut leanh::LeanObject,
    mut v___y_4915_: *mut leanh::LeanObject,
    mut v___y_4916_: *mut leanh::LeanObject,
    mut v___y_4917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4919_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_name_4912_, v___y_4917_);
    return v___x_4919_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___boxed(
    mut v_name_4920_: *mut leanh::LeanObject,
    mut v___y_4921_: *mut leanh::LeanObject,
    mut v___y_4922_: *mut leanh::LeanObject,
    mut v___y_4923_: *mut leanh::LeanObject,
    mut v___y_4924_: *mut leanh::LeanObject,
    mut v___y_4925_: *mut leanh::LeanObject,
    mut v___y_4926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4927_ =
        l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0(
            v_name_4920_,
            v___y_4921_,
            v___y_4922_,
            v___y_4923_,
            v___y_4924_,
            v___y_4925_,
        );
    leanh::lean_dec(v___y_4925_);
    leanh::lean_dec_ref(v___y_4924_);
    leanh::lean_dec(v___y_4923_);
    leanh::lean_dec_ref(v___y_4922_);
    leanh::lean_dec_ref(v___y_4921_);
    leanh::lean_dec(v_name_4920_);
    return v_res_4927_;
}
pub unsafe fn l_Lean_Server_locationLinksFromErrorNameInfo(
    mut v_eni_4928_: *mut leanh::LeanObject,
    mut v_a_4929_: *mut leanh::LeanObject,
    mut v_a_4930_: *mut leanh::LeanObject,
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
    mut v_a_4933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorName_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v_val_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declLoc_x3f_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4947_: u8 = 0;
    let mut v_module_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4952_: u8 = 0;
    let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4957_: u8 = 0;
    let mut v_val_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: u8 = 0;
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: u8 = 0;
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4979_: u8 = 0;
    let mut v_text_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4985_: u8 = 0;
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4990_: u8 = 0;
    let mut v_a_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4994_: u8 = 0;
    let mut v_ref_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_isSharedCheck_5009_: u8 = 0;
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stx_4935_ = leanh::lean_ctor_get(v_eni_4928_, 0);
                v_errorName_4936_ = leanh::lean_ctor_get(v_eni_4928_, 1);
                v___x_4937_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Server_locationLinksFromErrorNameInfo_spec__0___redArg(v_errorName_4936_, v_a_4933_);
                v_a_4938_ = leanh::lean_ctor_get(v___x_4937_, 0);
                v_isSharedCheck_5018_ = (!leanh::lean_is_exclusive(v___x_4937_)) as u8;
                if v_isSharedCheck_5018_ == 0 {
                    v___x_4940_ = v___x_4937_;
                    v_isShared_4941_ = v_isSharedCheck_5018_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4938_);
                    leanh::lean_dec(v___x_4937_);
                    v___x_4940_ = leanh::lean_box(0);
                    v_isShared_4941_ = v_isSharedCheck_5018_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4938_) == 1 {
                    v_val_4942_ = leanh::lean_ctor_get(v_a_4938_, 0);
                    leanh::lean_inc(v_val_4942_);
                    leanh::lean_dec_ref_known(v_a_4938_, 1);
                    v_declLoc_x3f_4943_ = leanh::lean_ctor_get(v_val_4942_, 2);
                    leanh::lean_inc(v_declLoc_x3f_4943_);
                    leanh::lean_dec(v_val_4942_);
                    if leanh::lean_obj_tag(v_declLoc_x3f_4943_) == 1 {
                        leanh::lean_del_object(v___x_4940_);
                        v_val_4944_ = leanh::lean_ctor_get(v_declLoc_x3f_4943_, 0);
                        v_isSharedCheck_5009_ =
                            (!leanh::lean_is_exclusive(v_declLoc_x3f_4943_)) as u8;
                        if v_isSharedCheck_5009_ == 0 {
                            v___x_4946_ = v_declLoc_x3f_4943_;
                            v_isShared_4947_ = v_isSharedCheck_5009_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4944_);
                            leanh::lean_dec(v_declLoc_x3f_4943_);
                            v___x_4946_ = leanh::lean_box(0);
                            v_isShared_4947_ = v_isSharedCheck_5009_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declLoc_x3f_4943_);
                        v___x_5010_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        if v_isShared_4941_ == 0 {
                            leanh::lean_ctor_set(v___x_4940_, 0, v___x_5010_);
                            v___x_5012_ = v___x_4940_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_5013_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_5010_);
                            v___x_5012_ = v_reuseFailAlloc_5013_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4938_);
                    v___x_5014_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4941_ == 0 {
                        leanh::lean_ctor_set(v___x_4940_, 0, v___x_5014_);
                        v___x_5016_ = v___x_4940_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_5017_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_5014_);
                        v___x_5016_ = v_reuseFailAlloc_5017_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_module_4948_ = leanh::lean_ctor_get(v_val_4944_, 0);
                v_range_4949_ = leanh::lean_ctor_get(v_val_4944_, 1);
                v_isSharedCheck_5008_ = (!leanh::lean_is_exclusive(v_val_4944_)) as u8;
                if v_isSharedCheck_5008_ == 0 {
                    v___x_4951_ = v_val_4944_;
                    v_isShared_4952_ = v_isSharedCheck_5008_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_range_4949_);
                    leanh::lean_inc(v_module_4948_);
                    leanh::lean_dec(v_val_4944_);
                    v___x_4951_ = leanh::lean_box(0);
                    v_isShared_4952_ = v_isSharedCheck_5008_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4953_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4948_);
                if leanh::lean_obj_tag(v___x_4953_) == 0 {
                    leanh::lean_del_object(v___x_4951_);
                    leanh::lean_del_object(v___x_4946_);
                    v_a_4954_ = leanh::lean_ctor_get(v___x_4953_, 0);
                    v_isSharedCheck_4990_ = (!leanh::lean_is_exclusive(v___x_4953_)) as u8;
                    if v_isSharedCheck_4990_ == 0 {
                        v___x_4956_ = v___x_4953_;
                        v_isShared_4957_ = v_isSharedCheck_4990_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4954_);
                        leanh::lean_dec(v___x_4953_);
                        v___x_4956_ = leanh::lean_box(0);
                        v_isShared_4957_ = v_isSharedCheck_4990_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_range_4949_);
                    v_a_4991_ = leanh::lean_ctor_get(v___x_4953_, 0);
                    v_isSharedCheck_5007_ = (!leanh::lean_is_exclusive(v___x_4953_)) as u8;
                    if v_isSharedCheck_5007_ == 0 {
                        v___x_4993_ = v___x_4953_;
                        v_isShared_4994_ = v_isSharedCheck_5007_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4991_);
                        leanh::lean_dec(v___x_4953_);
                        v___x_4993_ = leanh::lean_box(0);
                        v_isShared_4994_ = v_isSharedCheck_5007_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                if leanh::lean_obj_tag(v_a_4954_) == 1 {
                    v_val_4958_ = leanh::lean_ctor_get(v_a_4954_, 0);
                    leanh::lean_inc(v_val_4958_);
                    leanh::lean_dec_ref_known(v_a_4954_, 1);
                    v___x_4959_ = l_Lean_DeclarationRange_toLspRange(v_range_4949_);
                    v___x_4972_ = 1;
                    v___x_4973_ = l_Lean_Syntax_getRange_x3f(v_stx_4935_, v___x_4972_);
                    if leanh::lean_obj_tag(v___x_4973_) == 0 {
                        v___x_4974_ = leanh::lean_box(0);
                        v___y_4961_ = v___x_4974_;
                        state = 5;
                        continue;
                    } else {
                        v_doc_4975_ = leanh::lean_ctor_get(v_a_4929_, 0);
                        v_val_4976_ = leanh::lean_ctor_get(v___x_4973_, 0);
                        v_isSharedCheck_4985_ =
                            (!leanh::lean_is_exclusive(v___x_4973_)) as u8;
                        if v_isSharedCheck_4985_ == 0 {
                            v___x_4978_ = v___x_4973_;
                            v_isShared_4979_ = v_isSharedCheck_4985_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4976_);
                            leanh::lean_dec(v___x_4973_);
                            v___x_4978_ = leanh::lean_box(0);
                            v_isShared_4979_ = v_isSharedCheck_4985_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4954_);
                    leanh::lean_dec_ref(v_range_4949_);
                    v___x_4986_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_4957_ == 0 {
                        leanh::lean_ctor_set(v___x_4956_, 0, v___x_4986_);
                        v___x_4988_ = v___x_4956_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4986_);
                        v___x_4988_ = v_reuseFailAlloc_4989_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc_ref(v___x_4959_);
                v___x_4962_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4962_, 0, v___y_4961_);
                leanh::lean_ctor_set(v___x_4962_, 1, v_val_4958_);
                leanh::lean_ctor_set(v___x_4962_, 2, v___x_4959_);
                leanh::lean_ctor_set(v___x_4962_, 3, v___x_4959_);
                v___x_4963_ = leanh::lean_box(0);
                v___x_4964_ = 0;
                v___x_4965_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_4965_, 0, v___x_4962_);
                leanh::lean_ctor_set(v___x_4965_, 1, v___x_4963_);
                leanh::lean_ctor_set_uint8(
                    v___x_4965_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4964_,
                );
                v___x_4966_ = leanh::lean_unsigned_to_nat(1);
                v___x_4967_ = lean_mk_empty_array_with_capacity(v___x_4966_);
                v___x_4968_ = lean_array_push(v___x_4967_, v___x_4965_);
                if v_isShared_4957_ == 0 {
                    leanh::lean_ctor_set(v___x_4956_, 0, v___x_4968_);
                    v___x_4970_ = v___x_4956_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4971_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4968_);
                    v___x_4970_ = v_reuseFailAlloc_4971_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4970_;
            }
            7 => {
                v_text_4980_ = leanh::lean_ctor_get(v_doc_4975_, 3);
                leanh::lean_inc_ref(v_text_4980_);
                v___x_4981_ = l_Lean_Syntax_Range_toLspRange(v_text_4980_, v_val_4976_);
                if v_isShared_4979_ == 0 {
                    leanh::lean_ctor_set(v___x_4978_, 0, v___x_4981_);
                    v___x_4983_ = v___x_4978_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4984_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4984_, 0, v___x_4981_);
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
                v_ref_4995_ = leanh::lean_ctor_get(v_a_4932_, 5);
                v___x_4996_ = lean_io_error_to_string(v_a_4991_);
                if v_isShared_4947_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4946_, 3);
                    leanh::lean_ctor_set(v___x_4946_, 0, v___x_4996_);
                    v___x_4998_ = v___x_4946_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_4996_);
                    v___x_4998_ = v_reuseFailAlloc_5006_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4999_ = l_Lean_MessageData_ofFormat(v___x_4998_);
                leanh::lean_inc(v_ref_4995_);
                if v_isShared_4952_ == 0 {
                    leanh::lean_ctor_set(v___x_4951_, 1, v___x_4999_);
                    leanh::lean_ctor_set(v___x_4951_, 0, v_ref_4995_);
                    v___x_5001_ = v___x_4951_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_ref_4995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 1, v___x_4999_);
                    v___x_5001_ = v_reuseFailAlloc_5005_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4994_ == 0 {
                    leanh::lean_ctor_set(v___x_4993_, 0, v___x_5001_);
                    v___x_5003_ = v___x_4993_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5001_);
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
    mut v_eni_5019_: *mut leanh::LeanObject,
    mut v_a_5020_: *mut leanh::LeanObject,
    mut v_a_5021_: *mut leanh::LeanObject,
    mut v_a_5022_: *mut leanh::LeanObject,
    mut v_a_5023_: *mut leanh::LeanObject,
    mut v_a_5024_: *mut leanh::LeanObject,
    mut v_a_5025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5026_ = l_Lean_Server_locationLinksFromErrorNameInfo(
        v_eni_5019_,
        v_a_5020_,
        v_a_5021_,
        v_a_5022_,
        v_a_5023_,
        v_a_5024_,
    );
    leanh::lean_dec(v_a_5024_);
    leanh::lean_dec_ref(v_a_5023_);
    leanh::lean_dec(v_a_5022_);
    leanh::lean_dec_ref(v_a_5021_);
    leanh::lean_dec_ref(v_a_5020_);
    leanh::lean_dec_ref(v_eni_5019_);
    return v_res_5026_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(
    mut v_e_5027_: *mut leanh::LeanObject,
    mut v_a_5028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5036_: u8 = 0;
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5047_: u8 = 0;
    let mut v_a_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5055_: u8 = 0;
    let mut v_fn_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5064_: u8 = 0;
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5069_: u8 = 0;
    let mut v_expr_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_5027_) {
                4 => {
                    v_declName_5030_ = leanh::lean_ctor_get(v_e_5027_, 0);
                    leanh::lean_inc(v_declName_5030_);
                    leanh::lean_dec_ref_known(v_e_5027_, 2);
                    v___x_5031_ = l_Lean_Meta_isInstance___redArg(v_declName_5030_, v_a_5028_);
                    if leanh::lean_obj_tag(v___x_5031_) == 0 {
                        v_a_5032_ = leanh::lean_ctor_get(v___x_5031_, 0);
                        v_isSharedCheck_5047_ =
                            (!leanh::lean_is_exclusive(v___x_5031_)) as u8;
                        if v_isSharedCheck_5047_ == 0 {
                            v___x_5034_ = v___x_5031_;
                            v_isShared_5035_ = v_isSharedCheck_5047_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5032_);
                            leanh::lean_dec(v___x_5031_);
                            v___x_5034_ = leanh::lean_box(0);
                            v_isShared_5035_ = v_isSharedCheck_5047_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_5030_);
                        v_a_5048_ = leanh::lean_ctor_get(v___x_5031_, 0);
                        v_isSharedCheck_5055_ =
                            (!leanh::lean_is_exclusive(v___x_5031_)) as u8;
                        if v_isSharedCheck_5055_ == 0 {
                            v___x_5050_ = v___x_5031_;
                            v_isShared_5051_ = v_isSharedCheck_5055_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5048_);
                            leanh::lean_dec(v___x_5031_);
                            v___x_5050_ = leanh::lean_box(0);
                            v_isShared_5051_ = v_isSharedCheck_5055_;
                            state = 4;
                            continue;
                        }
                    }
                }
                5 => {
                    v_fn_5056_ = leanh::lean_ctor_get(v_e_5027_, 0);
                    leanh::lean_inc_ref(v_fn_5056_);
                    v_arg_5057_ = leanh::lean_ctor_get(v_e_5027_, 1);
                    leanh::lean_inc_ref(v_arg_5057_);
                    leanh::lean_dec_ref_known(v_e_5027_, 2);
                    v___x_5058_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_fn_5056_, v_a_5028_);
                    if leanh::lean_obj_tag(v___x_5058_) == 0 {
                        v_a_5059_ = leanh::lean_ctor_get(v___x_5058_, 0);
                        leanh::lean_inc(v_a_5059_);
                        leanh::lean_dec_ref_known(v___x_5058_, 1);
                        v___x_5060_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_arg_5057_, v_a_5028_);
                        if leanh::lean_obj_tag(v___x_5060_) == 0 {
                            v_a_5061_ = leanh::lean_ctor_get(v___x_5060_, 0);
                            v_isSharedCheck_5069_ =
                                (!leanh::lean_is_exclusive(v___x_5060_)) as u8;
                            if v_isSharedCheck_5069_ == 0 {
                                v___x_5063_ = v___x_5060_;
                                v_isShared_5064_ = v_isSharedCheck_5069_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5061_);
                                leanh::lean_dec(v___x_5060_);
                                v___x_5063_ = leanh::lean_box(0);
                                v_isShared_5064_ = v_isSharedCheck_5069_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5059_);
                            return v___x_5060_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_5057_);
                        return v___x_5058_;
                    }
                }
                10 => {
                    v_expr_5070_ = leanh::lean_ctor_get(v_e_5027_, 1);
                    leanh::lean_inc_ref(v_expr_5070_);
                    leanh::lean_dec_ref_known(v_e_5027_, 2);
                    v_e_5027_ = v_expr_5070_;
                    state = 0;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_e_5027_);
                    v___x_5072_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                    v___x_5073_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5073_, 0, v___x_5072_);
                    return v___x_5073_;
                }
            },
            1 => {
                v___x_5036_ = (leanh::lean_unbox(v_a_5032_) as u8);
                leanh::lean_dec(v_a_5032_);
                if v___x_5036_ == 0 {
                    leanh::lean_dec(v_declName_5030_);
                    v___x_5037_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksDefault_defaultDeclNames___redArg___closed__0;
                    if v_isShared_5035_ == 0 {
                        leanh::lean_ctor_set(v___x_5034_, 0, v___x_5037_);
                        v___x_5039_ = v___x_5034_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5040_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5037_);
                        v___x_5039_ = v_reuseFailAlloc_5040_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5041_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5042_ = lean_mk_empty_array_with_capacity(v___x_5041_);
                    v___x_5043_ = lean_array_push(v___x_5042_, v_declName_5030_);
                    if v_isShared_5035_ == 0 {
                        leanh::lean_ctor_set(v___x_5034_, 0, v___x_5043_);
                        v___x_5045_ = v___x_5034_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5046_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5043_);
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
                    v_reuseFailAlloc_5054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
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
                leanh::lean_dec(v_a_5059_);
                if v_isShared_5064_ == 0 {
                    leanh::lean_ctor_set(v___x_5063_, 0, v___x_5065_);
                    v___x_5067_ = v___x_5063_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5068_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 0, v___x_5065_);
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
    mut v_e_5074_: *mut leanh::LeanObject,
    mut v_a_5075_: *mut leanh::LeanObject,
    mut v_a_5076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5077_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_5074_, v_a_5075_);
    leanh::lean_dec(v_a_5075_);
    return v_res_5077_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(
    mut v_e_5078_: *mut leanh::LeanObject,
    mut v_a_5079_: *mut leanh::LeanObject,
    mut v_a_5080_: *mut leanh::LeanObject,
    mut v_a_5081_: *mut leanh::LeanObject,
    mut v_a_5082_: *mut leanh::LeanObject,
    mut v_a_5083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5085_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_e_5078_, v_a_5083_);
    return v___x_5085_;
}
pub unsafe fn l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___boxed(
    mut v_e_5086_: *mut leanh::LeanObject,
    mut v_a_5087_: *mut leanh::LeanObject,
    mut v_a_5088_: *mut leanh::LeanObject,
    mut v_a_5089_: *mut leanh::LeanObject,
    mut v_a_5090_: *mut leanh::LeanObject,
    mut v_a_5091_: *mut leanh::LeanObject,
    mut v_a_5092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5093_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances(v_e_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_, v_a_5091_);
    leanh::lean_dec(v_a_5091_);
    leanh::lean_dec_ref(v_a_5090_);
    leanh::lean_dec(v_a_5089_);
    leanh::lean_dec_ref(v_a_5088_);
    leanh::lean_dec_ref(v_a_5087_);
    return v_res_5093_;
}
pub unsafe fn l_Lean_Server_locationLinksFromInstanceProjection(
    mut v_e_5094_: *mut leanh::LeanObject,
    mut v_a_5095_: *mut leanh::LeanObject,
    mut v_a_5096_: *mut leanh::LeanObject,
    mut v_a_5097_: *mut leanh::LeanObject,
    mut v_a_5098_: *mut leanh::LeanObject,
    mut v_a_5099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5108_: u8 = 0;
    let mut v_val_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5113_: usize = 0;
    let mut v___x_5114_: usize = 0;
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut v_a_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5130_: u8 = 0;
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5134_: u8 = 0;
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5139_: u8 = 0;
    let mut v_a_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5143_: u8 = 0;
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5147_: u8 = 0;
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5101_ = l_Lean_Expr_getAppFn(v_e_5094_);
                v___x_5102_ = l_Lean_Expr_consumeMData(v___x_5101_);
                leanh::lean_dec_ref(v___x_5101_);
                if leanh::lean_obj_tag(v___x_5102_) == 4 {
                    v_declName_5103_ = leanh::lean_ctor_get(v___x_5102_, 0);
                    leanh::lean_inc(v_declName_5103_);
                    leanh::lean_dec_ref_known(v___x_5102_, 2);
                    v___x_5104_ = l_Lean_Server_getInstanceProjectionArg_x3f(
                        v_e_5094_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_,
                    );
                    if leanh::lean_obj_tag(v___x_5104_) == 0 {
                        v_a_5105_ = leanh::lean_ctor_get(v___x_5104_, 0);
                        v_isSharedCheck_5139_ =
                            (!leanh::lean_is_exclusive(v___x_5104_)) as u8;
                        if v_isSharedCheck_5139_ == 0 {
                            v___x_5107_ = v___x_5104_;
                            v_isShared_5108_ = v_isSharedCheck_5139_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5105_);
                            leanh::lean_dec(v___x_5104_);
                            v___x_5107_ = leanh::lean_box(0);
                            v_isShared_5108_ = v_isSharedCheck_5139_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_5103_);
                        v_a_5140_ = leanh::lean_ctor_get(v___x_5104_, 0);
                        v_isSharedCheck_5147_ =
                            (!leanh::lean_is_exclusive(v___x_5104_)) as u8;
                        if v_isSharedCheck_5147_ == 0 {
                            v___x_5142_ = v___x_5104_;
                            v_isShared_5143_ = v_isSharedCheck_5147_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5140_);
                            leanh::lean_dec(v___x_5104_);
                            v___x_5142_ = leanh::lean_box(0);
                            v_isShared_5143_ = v_isSharedCheck_5147_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5102_);
                    leanh::lean_dec_ref(v_e_5094_);
                    v___x_5148_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v___x_5149_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5149_, 0, v___x_5148_);
                    return v___x_5149_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5105_) == 1 {
                    leanh::lean_del_object(v___x_5107_);
                    v_val_5109_ = leanh::lean_ctor_get(v_a_5105_, 0);
                    leanh::lean_inc(v_val_5109_);
                    leanh::lean_dec_ref_known(v_a_5105_, 1);
                    v___x_5110_ = l___private_Lean_Server_GoTo_0__Lean_Server_locationLinksFromInstanceProjection_extractInstances___redArg(v_val_5109_, v_a_5099_);
                    if leanh::lean_obj_tag(v___x_5110_) == 0 {
                        v_a_5111_ = leanh::lean_ctor_get(v___x_5110_, 0);
                        leanh::lean_inc(v_a_5111_);
                        leanh::lean_dec_ref_known(v___x_5110_, 1);
                        v___x_5112_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                        v_sz_5113_ = lean_array_size(v_a_5111_);
                        v___x_5114_ = 0usize;
                        v___x_5115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksDefault_spec__0(v_a_5111_, v_sz_5113_, v___x_5114_, v___x_5112_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_);
                        leanh::lean_dec(v_a_5111_);
                        if leanh::lean_obj_tag(v___x_5115_) == 0 {
                            v_a_5116_ = leanh::lean_ctor_get(v___x_5115_, 0);
                            leanh::lean_inc(v_a_5116_);
                            leanh::lean_dec_ref_known(v___x_5115_, 1);
                            v___x_5117_ = l_Lean_Server_locationLinksFromDecl(
                                v_declName_5103_,
                                v_a_5095_,
                                v_a_5096_,
                                v_a_5097_,
                                v_a_5098_,
                                v_a_5099_,
                            );
                            if leanh::lean_obj_tag(v___x_5117_) == 0 {
                                v_a_5118_ = leanh::lean_ctor_get(v___x_5117_, 0);
                                v_isSharedCheck_5126_ =
                                    (!leanh::lean_is_exclusive(v___x_5117_)) as u8;
                                if v_isSharedCheck_5126_ == 0 {
                                    v___x_5120_ = v___x_5117_;
                                    v_isShared_5121_ = v_isSharedCheck_5126_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5118_);
                                    leanh::lean_dec(v___x_5117_);
                                    v___x_5120_ = leanh::lean_box(0);
                                    v_isShared_5121_ = v_isSharedCheck_5126_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5116_);
                                return v___x_5117_;
                            }
                        } else {
                            leanh::lean_dec(v_declName_5103_);
                            return v___x_5115_;
                        }
                    } else {
                        leanh::lean_dec(v_declName_5103_);
                        v_a_5127_ = leanh::lean_ctor_get(v___x_5110_, 0);
                        v_isSharedCheck_5134_ =
                            (!leanh::lean_is_exclusive(v___x_5110_)) as u8;
                        if v_isSharedCheck_5134_ == 0 {
                            v___x_5129_ = v___x_5110_;
                            v_isShared_5130_ = v_isSharedCheck_5134_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5127_);
                            leanh::lean_dec(v___x_5110_);
                            v___x_5129_ = leanh::lean_box(0);
                            v_isShared_5130_ = v_isSharedCheck_5134_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5105_);
                    leanh::lean_dec(v_declName_5103_);
                    v___x_5135_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_5108_ == 0 {
                        leanh::lean_ctor_set(v___x_5107_, 0, v___x_5135_);
                        v___x_5137_ = v___x_5107_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5138_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5135_);
                        v___x_5137_ = v_reuseFailAlloc_5138_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5122_ = l_Array_append___redArg(v_a_5116_, v_a_5118_);
                leanh::lean_dec(v_a_5118_);
                if v_isShared_5121_ == 0 {
                    leanh::lean_ctor_set(v___x_5120_, 0, v___x_5122_);
                    v___x_5124_ = v___x_5120_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5125_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5125_, 0, v___x_5122_);
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
                    v_reuseFailAlloc_5133_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
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
                    v_reuseFailAlloc_5146_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
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
    mut v_e_5150_: *mut leanh::LeanObject,
    mut v_a_5151_: *mut leanh::LeanObject,
    mut v_a_5152_: *mut leanh::LeanObject,
    mut v_a_5153_: *mut leanh::LeanObject,
    mut v_a_5154_: *mut leanh::LeanObject,
    mut v_a_5155_: *mut leanh::LeanObject,
    mut v_a_5156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5157_ = l_Lean_Server_locationLinksFromInstanceProjection(
        v_e_5150_, v_a_5151_, v_a_5152_, v_a_5153_, v_a_5154_, v_a_5155_,
    );
    leanh::lean_dec(v_a_5155_);
    leanh::lean_dec_ref(v_a_5154_);
    leanh::lean_dec(v_a_5153_);
    leanh::lean_dec_ref(v_a_5152_);
    leanh::lean_dec_ref(v_a_5151_);
    return v_res_5157_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(
    mut v_as_5158_: *mut leanh::LeanObject,
    mut v_sz_5159_: usize,
    mut v_i_5160_: usize,
    mut v_b_5161_: *mut leanh::LeanObject,
    mut v___y_5162_: *mut leanh::LeanObject,
    mut v___y_5163_: *mut leanh::LeanObject,
    mut v___y_5164_: *mut leanh::LeanObject,
    mut v___y_5165_: *mut leanh::LeanObject,
    mut v___y_5166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_newLL_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: usize = 0;
    let mut v___x_5172_: usize = 0;
    let mut v___x_5174_: u8 = 0;
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5174_ = lean_usize_dec_lt(v_i_5160_, v_sz_5159_);
                if v___x_5174_ == 0 {
                    v___x_5175_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5175_, 0, v_b_5161_);
                    return v___x_5175_;
                } else {
                    v_a_5176_ = lean_array_uget_borrowed(v_as_5158_, v_i_5160_);
                    v___x_5177_ = l_Lean_Expr_consumeMData(v_a_5176_);
                    match leanh::lean_obj_tag(v___x_5177_) {
                        4 => {
                            v_declName_5178_ = leanh::lean_ctor_get(v___x_5177_, 0);
                            leanh::lean_inc(v_declName_5178_);
                            leanh::lean_dec_ref_known(v___x_5177_, 2);
                            v___x_5179_ = l_Lean_Server_locationLinksFromDecl(
                                v_declName_5178_,
                                v___y_5162_,
                                v___y_5163_,
                                v___y_5164_,
                                v___y_5165_,
                                v___y_5166_,
                            );
                            if leanh::lean_obj_tag(v___x_5179_) == 0 {
                                v_a_5180_ = leanh::lean_ctor_get(v___x_5179_, 0);
                                leanh::lean_inc(v_a_5180_);
                                leanh::lean_dec_ref_known(v___x_5179_, 1);
                                v_newLL_5169_ = v_a_5180_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_5161_);
                                return v___x_5179_;
                            }
                        }
                        1 => {
                            v_fvarId_5181_ = leanh::lean_ctor_get(v___x_5177_, 0);
                            leanh::lean_inc(v_fvarId_5181_);
                            leanh::lean_dec_ref_known(v___x_5177_, 1);
                            v___x_5182_ = l_Lean_Server_locationLinksFromBinder___redArg(
                                v_fvarId_5181_,
                                v___y_5162_,
                            );
                            if leanh::lean_obj_tag(v___x_5182_) == 0 {
                                v_a_5183_ = leanh::lean_ctor_get(v___x_5182_, 0);
                                leanh::lean_inc(v_a_5183_);
                                leanh::lean_dec_ref_known(v___x_5182_, 1);
                                v_newLL_5169_ = v_a_5183_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_5161_);
                                return v___x_5182_;
                            }
                        }
                        _ => {
                            leanh::lean_dec_ref(v___x_5177_);
                            leanh::lean_inc(v_a_5176_);
                            v___x_5184_ = l_Lean_Server_locationLinksFromInstanceProjection(
                                v_a_5176_,
                                v___y_5162_,
                                v___y_5163_,
                                v___y_5164_,
                                v___y_5165_,
                                v___y_5166_,
                            );
                            if leanh::lean_obj_tag(v___x_5184_) == 0 {
                                v_a_5185_ = leanh::lean_ctor_get(v___x_5184_, 0);
                                leanh::lean_inc(v_a_5185_);
                                leanh::lean_dec_ref_known(v___x_5184_, 1);
                                v_newLL_5169_ = v_a_5185_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_5161_);
                                return v___x_5184_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5170_ = l_Array_append___redArg(v_b_5161_, v_newLL_5169_);
                leanh::lean_dec_ref(v_newLL_5169_);
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
    mut v_as_5186_: *mut leanh::LeanObject,
    mut v_sz_5187_: *mut leanh::LeanObject,
    mut v_i_5188_: *mut leanh::LeanObject,
    mut v_b_5189_: *mut leanh::LeanObject,
    mut v___y_5190_: *mut leanh::LeanObject,
    mut v___y_5191_: *mut leanh::LeanObject,
    mut v___y_5192_: *mut leanh::LeanObject,
    mut v___y_5193_: *mut leanh::LeanObject,
    mut v___y_5194_: *mut leanh::LeanObject,
    mut v___y_5195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5196_: usize = 0;
    let mut v_i_boxed_5197_: usize = 0;
    let mut v_res_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5196_ = leanh::lean_unbox_usize(v_sz_5187_);
    leanh::lean_dec(v_sz_5187_);
    v_i_boxed_5197_ = leanh::lean_unbox_usize(v_i_5188_);
    leanh::lean_dec(v_i_5188_);
    v_res_5198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_as_5186_, v_sz_boxed_5196_, v_i_boxed_5197_, v_b_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
    leanh::lean_dec(v___y_5194_);
    leanh::lean_dec_ref(v___y_5193_);
    leanh::lean_dec(v___y_5192_);
    leanh::lean_dec_ref(v___y_5191_);
    leanh::lean_dec_ref(v___y_5190_);
    leanh::lean_dec_ref(v_as_5186_);
    return v_res_5198_;
}
pub unsafe fn l_Lean_Server_locationLinksFromTermInfo(
    mut v_ti_5199_: *mut leanh::LeanObject,
    mut v_a_5200_: *mut leanh::LeanObject,
    mut v_a_5201_: *mut leanh::LeanObject,
    mut v_a_5202_: *mut leanh::LeanObject,
    mut v_a_5203_: *mut leanh::LeanObject,
    mut v_a_5204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_5206_: u8 = 0;
    let mut v___x_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5210_: usize = 0;
    let mut v___x_5211_: usize = 0;
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5216_: u8 = 0;
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_5206_ = leanh::lean_ctor_get_uint8(
                    v_a_5200_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                );
                v___x_5207_ = l_Lean_Server_GoToKind_determineTargetExprs(
                    v_kind_5206_,
                    v_ti_5199_,
                    v_a_5201_,
                    v_a_5202_,
                    v_a_5203_,
                    v_a_5204_,
                );
                if leanh::lean_obj_tag(v___x_5207_) == 0 {
                    v_a_5208_ = leanh::lean_ctor_get(v___x_5207_, 0);
                    leanh::lean_inc(v_a_5208_);
                    leanh::lean_dec_ref_known(v___x_5207_, 1);
                    v___x_5209_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    v_sz_5210_ = lean_array_size(v_a_5208_);
                    v___x_5211_ = 0usize;
                    v___x_5212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_locationLinksFromTermInfo_spec__0(v_a_5208_, v_sz_5210_, v___x_5211_, v___x_5209_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
                    leanh::lean_dec(v_a_5208_);
                    return v___x_5212_;
                } else {
                    v_a_5213_ = leanh::lean_ctor_get(v___x_5207_, 0);
                    v_isSharedCheck_5220_ = (!leanh::lean_is_exclusive(v___x_5207_)) as u8;
                    if v_isSharedCheck_5220_ == 0 {
                        v___x_5215_ = v___x_5207_;
                        v_isShared_5216_ = v_isSharedCheck_5220_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5213_);
                        leanh::lean_dec(v___x_5207_);
                        v___x_5215_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
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
    mut v_ti_5221_: *mut leanh::LeanObject,
    mut v_a_5222_: *mut leanh::LeanObject,
    mut v_a_5223_: *mut leanh::LeanObject,
    mut v_a_5224_: *mut leanh::LeanObject,
    mut v_a_5225_: *mut leanh::LeanObject,
    mut v_a_5226_: *mut leanh::LeanObject,
    mut v_a_5227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5228_ = l_Lean_Server_locationLinksFromTermInfo(
        v_ti_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_,
    );
    leanh::lean_dec(v_a_5226_);
    leanh::lean_dec_ref(v_a_5225_);
    leanh::lean_dec(v_a_5224_);
    leanh::lean_dec_ref(v_a_5223_);
    leanh::lean_dec_ref(v_a_5222_);
    return v_res_5228_;
}
pub unsafe fn l_Lean_Server_locationLinksFromDelabTermInfo(
    mut v_dti_5229_: *mut leanh::LeanObject,
    mut v_a_5230_: *mut leanh::LeanObject,
    mut v_a_5231_: *mut leanh::LeanObject,
    mut v_a_5232_: *mut leanh::LeanObject,
    mut v_a_5233_: *mut leanh::LeanObject,
    mut v_a_5234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_location_x3f_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5240_: u8 = 0;
    let mut v_toTermInfo_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5246_: u8 = 0;
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v_val_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5255_: u8 = 0;
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5277_: u8 = 0;
    let mut v_text_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v_reuseFailAlloc_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5285_: u8 = 0;
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5287_: u8 = 0;
    let mut v_a_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5291_: u8 = 0;
    let mut v_ref_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5304_: u8 = 0;
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut v_isSharedCheck_5306_: u8 = 0;
    let mut v_toTermInfo_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_location_x3f_5236_ = leanh::lean_ctor_get(v_dti_5229_, 1);
                leanh::lean_inc(v_location_x3f_5236_);
                if leanh::lean_obj_tag(v_location_x3f_5236_) == 1 {
                    v_val_5237_ = leanh::lean_ctor_get(v_location_x3f_5236_, 0);
                    v_isSharedCheck_5306_ =
                        (!leanh::lean_is_exclusive(v_location_x3f_5236_)) as u8;
                    if v_isSharedCheck_5306_ == 0 {
                        v___x_5239_ = v_location_x3f_5236_;
                        v_isShared_5240_ = v_isSharedCheck_5306_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5237_);
                        leanh::lean_dec(v_location_x3f_5236_);
                        v___x_5239_ = leanh::lean_box(0);
                        v_isShared_5240_ = v_isSharedCheck_5306_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_location_x3f_5236_);
                    v_toTermInfo_5307_ = leanh::lean_ctor_get(v_dti_5229_, 0);
                    leanh::lean_inc_ref(v_toTermInfo_5307_);
                    leanh::lean_dec_ref(v_dti_5229_);
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
                v_toTermInfo_5241_ = leanh::lean_ctor_get(v_dti_5229_, 0);
                v_module_5242_ = leanh::lean_ctor_get(v_val_5237_, 0);
                v_range_5243_ = leanh::lean_ctor_get(v_val_5237_, 1);
                v_isSharedCheck_5305_ = (!leanh::lean_is_exclusive(v_val_5237_)) as u8;
                if v_isSharedCheck_5305_ == 0 {
                    v___x_5245_ = v_val_5237_;
                    v_isShared_5246_ = v_isSharedCheck_5305_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_range_5243_);
                    leanh::lean_inc(v_module_5242_);
                    leanh::lean_dec(v_val_5237_);
                    v___x_5245_ = leanh::lean_box(0);
                    v_isShared_5246_ = v_isSharedCheck_5305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5247_ = l_Lean_Server_documentUriFromModule_x3f(v_module_5242_);
                if leanh::lean_obj_tag(v___x_5247_) == 0 {
                    leanh::lean_del_object(v___x_5245_);
                    leanh::lean_del_object(v___x_5239_);
                    v_a_5248_ = leanh::lean_ctor_get(v___x_5247_, 0);
                    v_isSharedCheck_5287_ = (!leanh::lean_is_exclusive(v___x_5247_)) as u8;
                    if v_isSharedCheck_5287_ == 0 {
                        v___x_5250_ = v___x_5247_;
                        v_isShared_5251_ = v_isSharedCheck_5287_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5248_);
                        leanh::lean_dec(v___x_5247_);
                        v___x_5250_ = leanh::lean_box(0);
                        v_isShared_5251_ = v_isSharedCheck_5287_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_range_5243_);
                    leanh::lean_dec_ref(v_dti_5229_);
                    v_a_5288_ = leanh::lean_ctor_get(v___x_5247_, 0);
                    v_isSharedCheck_5304_ = (!leanh::lean_is_exclusive(v___x_5247_)) as u8;
                    if v_isSharedCheck_5304_ == 0 {
                        v___x_5290_ = v___x_5247_;
                        v_isShared_5291_ = v_isSharedCheck_5304_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5288_);
                        leanh::lean_dec(v___x_5247_);
                        v___x_5290_ = leanh::lean_box(0);
                        v_isShared_5291_ = v_isSharedCheck_5304_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_5248_) == 1 {
                    v_val_5252_ = leanh::lean_ctor_get(v_a_5248_, 0);
                    v_isSharedCheck_5285_ = (!leanh::lean_is_exclusive(v_a_5248_)) as u8;
                    if v_isSharedCheck_5285_ == 0 {
                        v___x_5254_ = v_a_5248_;
                        v_isShared_5255_ = v_isSharedCheck_5285_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5252_);
                        leanh::lean_dec(v_a_5248_);
                        v___x_5254_ = leanh::lean_box(0);
                        v_isShared_5255_ = v_isSharedCheck_5285_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_toTermInfo_5241_);
                    leanh::lean_del_object(v___x_5250_);
                    leanh::lean_dec(v_a_5248_);
                    leanh::lean_dec_ref(v_range_5243_);
                    leanh::lean_dec_ref(v_dti_5229_);
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
                    leanh::lean_ctor_set_tag(v___x_5254_, 13);
                    leanh::lean_ctor_set(v___x_5254_, 0, v_dti_5229_);
                    v___x_5270_ = v___x_5254_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5284_ = leanh::lean_alloc_ctor(13, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5284_, 0, v_dti_5229_);
                    v___x_5270_ = v_reuseFailAlloc_5284_;
                    state = 7;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___x_5256_);
                v___x_5259_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5259_, 0, v___y_5258_);
                leanh::lean_ctor_set(v___x_5259_, 1, v_val_5252_);
                leanh::lean_ctor_set(v___x_5259_, 2, v___x_5256_);
                leanh::lean_ctor_set(v___x_5259_, 3, v___x_5256_);
                v___x_5260_ = leanh::lean_box(0);
                v___x_5261_ = 0;
                v___x_5262_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_5262_, 0, v___x_5259_);
                leanh::lean_ctor_set(v___x_5262_, 1, v___x_5260_);
                leanh::lean_ctor_set_uint8(
                    v___x_5262_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5261_,
                );
                v___x_5263_ = leanh::lean_unsigned_to_nat(1);
                v___x_5264_ = lean_mk_empty_array_with_capacity(v___x_5263_);
                v___x_5265_ = lean_array_push(v___x_5264_, v___x_5262_);
                if v_isShared_5251_ == 0 {
                    leanh::lean_ctor_set(v___x_5250_, 0, v___x_5265_);
                    v___x_5267_ = v___x_5250_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5268_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5268_, 0, v___x_5265_);
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
                leanh::lean_dec_ref(v___x_5270_);
                if leanh::lean_obj_tag(v___x_5271_) == 0 {
                    v___x_5272_ = leanh::lean_box(0);
                    v___y_5258_ = v___x_5272_;
                    state = 5;
                    continue;
                } else {
                    v_doc_5273_ = leanh::lean_ctor_get(v_a_5230_, 0);
                    v_val_5274_ = leanh::lean_ctor_get(v___x_5271_, 0);
                    v_isSharedCheck_5283_ = (!leanh::lean_is_exclusive(v___x_5271_)) as u8;
                    if v_isSharedCheck_5283_ == 0 {
                        v___x_5276_ = v___x_5271_;
                        v_isShared_5277_ = v_isSharedCheck_5283_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5274_);
                        leanh::lean_dec(v___x_5271_);
                        v___x_5276_ = leanh::lean_box(0);
                        v_isShared_5277_ = v_isSharedCheck_5283_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v_text_5278_ = leanh::lean_ctor_get(v_doc_5273_, 3);
                leanh::lean_inc_ref(v_text_5278_);
                v___x_5279_ = l_Lean_Syntax_Range_toLspRange(v_text_5278_, v_val_5274_);
                if v_isShared_5277_ == 0 {
                    leanh::lean_ctor_set(v___x_5276_, 0, v___x_5279_);
                    v___x_5281_ = v___x_5276_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5279_);
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
                v_ref_5292_ = leanh::lean_ctor_get(v_a_5233_, 5);
                v___x_5293_ = lean_io_error_to_string(v_a_5288_);
                if v_isShared_5240_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5239_, 3);
                    leanh::lean_ctor_set(v___x_5239_, 0, v___x_5293_);
                    v___x_5295_ = v___x_5239_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5303_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5293_);
                    v___x_5295_ = v_reuseFailAlloc_5303_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_5296_ = l_Lean_MessageData_ofFormat(v___x_5295_);
                leanh::lean_inc(v_ref_5292_);
                if v_isShared_5246_ == 0 {
                    leanh::lean_ctor_set(v___x_5245_, 1, v___x_5296_);
                    leanh::lean_ctor_set(v___x_5245_, 0, v_ref_5292_);
                    v___x_5298_ = v___x_5245_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5302_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_ref_5292_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5302_, 1, v___x_5296_);
                    v___x_5298_ = v_reuseFailAlloc_5302_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_5291_ == 0 {
                    leanh::lean_ctor_set(v___x_5290_, 0, v___x_5298_);
                    v___x_5300_ = v___x_5290_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5301_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5298_);
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
    mut v_dti_5309_: *mut leanh::LeanObject,
    mut v_a_5310_: *mut leanh::LeanObject,
    mut v_a_5311_: *mut leanh::LeanObject,
    mut v_a_5312_: *mut leanh::LeanObject,
    mut v_a_5313_: *mut leanh::LeanObject,
    mut v_a_5314_: *mut leanh::LeanObject,
    mut v_a_5315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5316_ = l_Lean_Server_locationLinksFromDelabTermInfo(
        v_dti_5309_,
        v_a_5310_,
        v_a_5311_,
        v_a_5312_,
        v_a_5313_,
        v_a_5314_,
    );
    leanh::lean_dec(v_a_5314_);
    leanh::lean_dec_ref(v_a_5313_);
    leanh::lean_dec(v_a_5312_);
    leanh::lean_dec_ref(v_a_5311_);
    leanh::lean_dec_ref(v_a_5310_);
    return v_res_5316_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(
    mut v_e_5317_: *mut leanh::LeanObject,
    mut v___y_5318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5320_: u8 = 0;
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5334_: u8 = 0;
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5340_: u8 = 0;
    let mut v_unused_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5320_ = l_Lean_Expr_hasMVar(v_e_5317_);
                if v___x_5320_ == 0 {
                    v___x_5321_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5321_, 0, v_e_5317_);
                    return v___x_5321_;
                } else {
                    v___x_5322_ = lean_st_ref_get(v___y_5318_);
                    v_mctx_5323_ = leanh::lean_ctor_get(v___x_5322_, 0);
                    leanh::lean_inc_ref(v_mctx_5323_);
                    leanh::lean_dec(v___x_5322_);
                    v___x_5324_ = l_Lean_instantiateMVarsCore(v_mctx_5323_, v_e_5317_);
                    v_fst_5325_ = leanh::lean_ctor_get(v___x_5324_, 0);
                    leanh::lean_inc(v_fst_5325_);
                    v_snd_5326_ = leanh::lean_ctor_get(v___x_5324_, 1);
                    leanh::lean_inc(v_snd_5326_);
                    leanh::lean_dec_ref(v___x_5324_);
                    v___x_5327_ = lean_st_ref_take(v___y_5318_);
                    v_cache_5328_ = leanh::lean_ctor_get(v___x_5327_, 1);
                    v_zetaDeltaFVarIds_5329_ = leanh::lean_ctor_get(v___x_5327_, 2);
                    v_postponed_5330_ = leanh::lean_ctor_get(v___x_5327_, 3);
                    v_diag_5331_ = leanh::lean_ctor_get(v___x_5327_, 4);
                    v_isSharedCheck_5340_ = (!leanh::lean_is_exclusive(v___x_5327_)) as u8;
                    if v_isSharedCheck_5340_ == 0 {
                        v_unused_5341_ = leanh::lean_ctor_get(v___x_5327_, 0);
                        leanh::lean_dec(v_unused_5341_);
                        v___x_5333_ = v___x_5327_;
                        v_isShared_5334_ = v_isSharedCheck_5340_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_5331_);
                        leanh::lean_inc(v_postponed_5330_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_5329_);
                        leanh::lean_inc(v_cache_5328_);
                        leanh::lean_dec(v___x_5327_);
                        v___x_5333_ = leanh::lean_box(0);
                        v_isShared_5334_ = v_isSharedCheck_5340_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5334_ == 0 {
                    leanh::lean_ctor_set(v___x_5333_, 0, v_snd_5326_);
                    v___x_5336_ = v___x_5333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5339_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_snd_5326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 1, v_cache_5328_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5339_,
                        2,
                        v_zetaDeltaFVarIds_5329_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 3, v_postponed_5330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 4, v_diag_5331_);
                    v___x_5336_ = v_reuseFailAlloc_5339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5337_ = lean_st_ref_set(v___y_5318_, v___x_5336_);
                v___x_5338_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5338_, 0, v_fst_5325_);
                return v___x_5338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg___boxed(
    mut v_e_5342_: *mut leanh::LeanObject,
    mut v___y_5343_: *mut leanh::LeanObject,
    mut v___y_5344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5345_ =
        l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(
            v_e_5342_,
            v___y_5343_,
        );
    leanh::lean_dec(v___y_5343_);
    return v_res_5345_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(
    mut v_e_5346_: *mut leanh::LeanObject,
    mut v___y_5347_: *mut leanh::LeanObject,
    mut v___y_5348_: *mut leanh::LeanObject,
    mut v___y_5349_: *mut leanh::LeanObject,
    mut v___y_5350_: *mut leanh::LeanObject,
    mut v___y_5351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5353_ =
        l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(
            v_e_5346_,
            v___y_5349_,
        );
    return v___x_5353_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___boxed(
    mut v_e_5354_: *mut leanh::LeanObject,
    mut v___y_5355_: *mut leanh::LeanObject,
    mut v___y_5356_: *mut leanh::LeanObject,
    mut v___y_5357_: *mut leanh::LeanObject,
    mut v___y_5358_: *mut leanh::LeanObject,
    mut v___y_5359_: *mut leanh::LeanObject,
    mut v___y_5360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5361_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0(
        v_e_5354_,
        v___y_5355_,
        v___y_5356_,
        v___y_5357_,
        v___y_5358_,
        v___y_5359_,
    );
    leanh::lean_dec(v___y_5359_);
    leanh::lean_dec_ref(v___y_5358_);
    leanh::lean_dec(v___y_5357_);
    leanh::lean_dec_ref(v___y_5356_);
    leanh::lean_dec_ref(v___y_5355_);
    return v_res_5361_;
}
pub unsafe fn l_Lean_Server_locationLinksFromFieldInfo(
    mut v_fi_5362_: *mut leanh::LeanObject,
    mut v_a_5363_: *mut leanh::LeanObject,
    mut v_a_5364_: *mut leanh::LeanObject,
    mut v_a_5365_: *mut leanh::LeanObject,
    mut v_a_5366_: *mut leanh::LeanObject,
    mut v_a_5367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_5369_: u8 = 0;
    let mut v___x_5370_: u8 = 0;
    let mut v___x_5371_: u8 = 0;
    let mut v_projName_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5381_: u8 = 0;
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5390_: u8 = 0;
    let mut v_a_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_5369_ = leanh::lean_ctor_get_uint8(
                    v_a_5363_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                );
                v___x_5370_ = 2;
                v___x_5371_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_5369_, v___x_5370_);
                if v___x_5371_ == 0 {
                    v_projName_5372_ = leanh::lean_ctor_get(v_fi_5362_, 0);
                    leanh::lean_inc(v_projName_5372_);
                    leanh::lean_dec_ref(v_fi_5362_);
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
                    v_val_5374_ = leanh::lean_ctor_get(v_fi_5362_, 3);
                    leanh::lean_inc_ref(v_val_5374_);
                    leanh::lean_dec_ref(v_fi_5362_);
                    leanh::lean_inc(v_a_5367_);
                    leanh::lean_inc_ref(v_a_5366_);
                    leanh::lean_inc(v_a_5365_);
                    leanh::lean_inc_ref(v_a_5364_);
                    v___x_5375_ =
                        lean_infer_type(v_val_5374_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_);
                    if leanh::lean_obj_tag(v___x_5375_) == 0 {
                        v_a_5376_ = leanh::lean_ctor_get(v___x_5375_, 0);
                        leanh::lean_inc(v_a_5376_);
                        leanh::lean_dec_ref_known(v___x_5375_, 1);
                        v___x_5377_ = l_Lean_instantiateMVars___at___00Lean_Server_locationLinksFromFieldInfo_spec__0___redArg(v_a_5376_, v_a_5365_);
                        v_a_5378_ = leanh::lean_ctor_get(v___x_5377_, 0);
                        v_isSharedCheck_5390_ =
                            (!leanh::lean_is_exclusive(v___x_5377_)) as u8;
                        if v_isSharedCheck_5390_ == 0 {
                            v___x_5380_ = v___x_5377_;
                            v_isShared_5381_ = v_isSharedCheck_5390_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5378_);
                            leanh::lean_dec(v___x_5377_);
                            v___x_5380_ = leanh::lean_box(0);
                            v_isShared_5381_ = v_isSharedCheck_5390_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5391_ = leanh::lean_ctor_get(v___x_5375_, 0);
                        v_isSharedCheck_5398_ =
                            (!leanh::lean_is_exclusive(v___x_5375_)) as u8;
                        if v_isSharedCheck_5398_ == 0 {
                            v___x_5393_ = v___x_5375_;
                            v_isShared_5394_ = v_isSharedCheck_5398_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5391_);
                            leanh::lean_dec(v___x_5375_);
                            v___x_5393_ = leanh::lean_box(0);
                            v_isShared_5394_ = v_isSharedCheck_5398_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5382_ = l_Lean_Expr_getAppFn(v_a_5378_);
                leanh::lean_dec(v_a_5378_);
                v___x_5383_ = l_Lean_Expr_constName_x3f(v___x_5382_);
                leanh::lean_dec_ref(v___x_5382_);
                if leanh::lean_obj_tag(v___x_5383_) == 1 {
                    leanh::lean_del_object(v___x_5380_);
                    v_val_5384_ = leanh::lean_ctor_get(v___x_5383_, 0);
                    leanh::lean_inc(v_val_5384_);
                    leanh::lean_dec_ref_known(v___x_5383_, 1);
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
                    leanh::lean_dec(v___x_5383_);
                    v___x_5386_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                    if v_isShared_5381_ == 0 {
                        leanh::lean_ctor_set(v___x_5380_, 0, v___x_5386_);
                        v___x_5388_ = v___x_5380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5389_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5389_, 0, v___x_5386_);
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
                    v_reuseFailAlloc_5397_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_a_5391_);
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
    mut v_fi_5399_: *mut leanh::LeanObject,
    mut v_a_5400_: *mut leanh::LeanObject,
    mut v_a_5401_: *mut leanh::LeanObject,
    mut v_a_5402_: *mut leanh::LeanObject,
    mut v_a_5403_: *mut leanh::LeanObject,
    mut v_a_5404_: *mut leanh::LeanObject,
    mut v_a_5405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5406_ = l_Lean_Server_locationLinksFromFieldInfo(
        v_fi_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_,
    );
    leanh::lean_dec(v_a_5404_);
    leanh::lean_dec_ref(v_a_5403_);
    leanh::lean_dec(v_a_5402_);
    leanh::lean_dec_ref(v_a_5401_);
    leanh::lean_dec_ref(v_a_5400_);
    return v_res_5406_;
}
pub unsafe fn l_Lean_Server_locationLinksFromOptionInfo(
    mut v_i_5407_: *mut leanh::LeanObject,
    mut v_a_5408_: *mut leanh::LeanObject,
    mut v_a_5409_: *mut leanh::LeanObject,
    mut v_a_5410_: *mut leanh::LeanObject,
    mut v_a_5411_: *mut leanh::LeanObject,
    mut v_a_5412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_declName_5414_ = leanh::lean_ctor_get(v_i_5407_, 2);
    leanh::lean_inc(v_declName_5414_);
    leanh::lean_dec_ref(v_i_5407_);
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
    mut v_i_5416_: *mut leanh::LeanObject,
    mut v_a_5417_: *mut leanh::LeanObject,
    mut v_a_5418_: *mut leanh::LeanObject,
    mut v_a_5419_: *mut leanh::LeanObject,
    mut v_a_5420_: *mut leanh::LeanObject,
    mut v_a_5421_: *mut leanh::LeanObject,
    mut v_a_5422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5423_ = l_Lean_Server_locationLinksFromOptionInfo(
        v_i_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_,
    );
    leanh::lean_dec(v_a_5421_);
    leanh::lean_dec_ref(v_a_5420_);
    leanh::lean_dec(v_a_5419_);
    leanh::lean_dec_ref(v_a_5418_);
    leanh::lean_dec_ref(v_a_5417_);
    return v_res_5423_;
}
pub unsafe fn l_Lean_Server_locationLinksFromCommandInfo___redArg(
    mut v_i_5424_: *mut leanh::LeanObject,
    mut v_a_5425_: *mut leanh::LeanObject,
    mut v_a_5426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elaborator_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: u8 = 0;
    let mut v_kind_5436_: u8 = 0;
    let mut v___x_5437_: u8 = 0;
    let mut v___x_5438_: u8 = 0;
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elaborator_5431_ = leanh::lean_ctor_get(v_i_5424_, 0);
                if leanh::lean_obj_tag(v_elaborator_5431_) == 1 {
                    v_pre_5432_ = leanh::lean_ctor_get(v_elaborator_5431_, 0);
                    if leanh::lean_obj_tag(v_pre_5432_) == 0 {
                        v_str_5433_ = leanh::lean_ctor_get(v_elaborator_5431_, 1);
                        v___x_5434_ = l_Lean_Server_locationLinksFromImport___redArg___closed__3;
                        v___x_5435_ = lean_string_dec_eq(v_str_5433_, v___x_5434_);
                        if v___x_5435_ == 0 {
                            leanh::lean_dec_ref(v_i_5424_);
                            state = 1;
                            continue;
                        } else {
                            v_kind_5436_ = leanh::lean_ctor_get_uint8(
                                v_a_5425_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
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
                                leanh::lean_dec_ref(v_i_5424_);
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_i_5424_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_i_5424_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5429_ = l_Lean_Server_locationLinksFromDecl___closed__0;
                v___x_5430_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5430_, 0, v___x_5429_);
                return v___x_5430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksFromCommandInfo___redArg___boxed(
    mut v_i_5440_: *mut leanh::LeanObject,
    mut v_a_5441_: *mut leanh::LeanObject,
    mut v_a_5442_: *mut leanh::LeanObject,
    mut v_a_5443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5444_ =
        l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_5440_, v_a_5441_, v_a_5442_);
    leanh::lean_dec_ref(v_a_5442_);
    leanh::lean_dec_ref(v_a_5441_);
    return v_res_5444_;
}
pub unsafe fn l_Lean_Server_locationLinksFromCommandInfo(
    mut v_i_5445_: *mut leanh::LeanObject,
    mut v_a_5446_: *mut leanh::LeanObject,
    mut v_a_5447_: *mut leanh::LeanObject,
    mut v_a_5448_: *mut leanh::LeanObject,
    mut v_a_5449_: *mut leanh::LeanObject,
    mut v_a_5450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5452_ =
        l_Lean_Server_locationLinksFromCommandInfo___redArg(v_i_5445_, v_a_5446_, v_a_5449_);
    return v___x_5452_;
}
pub unsafe fn l_Lean_Server_locationLinksFromCommandInfo___boxed(
    mut v_i_5453_: *mut leanh::LeanObject,
    mut v_a_5454_: *mut leanh::LeanObject,
    mut v_a_5455_: *mut leanh::LeanObject,
    mut v_a_5456_: *mut leanh::LeanObject,
    mut v_a_5457_: *mut leanh::LeanObject,
    mut v_a_5458_: *mut leanh::LeanObject,
    mut v_a_5459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5460_ = l_Lean_Server_locationLinksFromCommandInfo(
        v_i_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_,
    );
    leanh::lean_dec(v_a_5458_);
    leanh::lean_dec_ref(v_a_5457_);
    leanh::lean_dec(v_a_5456_);
    leanh::lean_dec_ref(v_a_5455_);
    leanh::lean_dec_ref(v_a_5454_);
    return v_res_5460_;
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo___lam__0(
    mut v_kind_5461_: u8,
    mut v_ll_5462_: *mut leanh::LeanObject,
    mut v___y_5463_: *mut leanh::LeanObject,
    mut v___y_5464_: *mut leanh::LeanObject,
    mut v___y_5465_: *mut leanh::LeanObject,
    mut v___y_5466_: *mut leanh::LeanObject,
    mut v___y_5467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5470_: u8 = 0;
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5476_: u8 = 0;
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5481_: u8 = 0;
    let mut v___x_5482_: u8 = 0;
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5482_ = 0;
                v___x_5483_ = l_Lean_Server_instBEqGoToKind_beq(v_kind_5461_, v___x_5482_);
                if v___x_5483_ == 0 {
                    v___x_5484_ = lean_array_get_size(v_ll_5462_);
                    v___x_5485_ = leanh::lean_unsigned_to_nat(0);
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
                    v___x_5471_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5471_, 0, v_ll_5462_);
                    return v___x_5471_;
                } else {
                    v___x_5472_ = l_Lean_Server_locationLinksDefault(
                        v___y_5463_,
                        v___y_5464_,
                        v___y_5465_,
                        v___y_5466_,
                        v___y_5467_,
                    );
                    if leanh::lean_obj_tag(v___x_5472_) == 0 {
                        v_a_5473_ = leanh::lean_ctor_get(v___x_5472_, 0);
                        v_isSharedCheck_5481_ =
                            (!leanh::lean_is_exclusive(v___x_5472_)) as u8;
                        if v_isSharedCheck_5481_ == 0 {
                            v___x_5475_ = v___x_5472_;
                            v_isShared_5476_ = v_isSharedCheck_5481_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5473_);
                            leanh::lean_dec(v___x_5472_);
                            v___x_5475_ = leanh::lean_box(0);
                            v_isShared_5476_ = v_isSharedCheck_5481_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_ll_5462_);
                        return v___x_5472_;
                    }
                }
            }
            2 => {
                v___x_5477_ = l_Array_append___redArg(v_ll_5462_, v_a_5473_);
                leanh::lean_dec(v_a_5473_);
                if v_isShared_5476_ == 0 {
                    leanh::lean_ctor_set(v___x_5475_, 0, v___x_5477_);
                    v___x_5479_ = v___x_5475_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5480_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5477_);
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
    mut v_kind_5487_: *mut leanh::LeanObject,
    mut v_ll_5488_: *mut leanh::LeanObject,
    mut v___y_5489_: *mut leanh::LeanObject,
    mut v___y_5490_: *mut leanh::LeanObject,
    mut v___y_5491_: *mut leanh::LeanObject,
    mut v___y_5492_: *mut leanh::LeanObject,
    mut v___y_5493_: *mut leanh::LeanObject,
    mut v___y_5494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_5495_: u8 = 0;
    let mut v_res_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5495_ = (leanh::lean_unbox(v_kind_5487_) as u8);
    v_res_5496_ = l_Lean_Server_locationLinksOfInfo___lam__0(
        v_kind_boxed_5495_,
        v_ll_5488_,
        v___y_5489_,
        v___y_5490_,
        v___y_5491_,
        v___y_5492_,
        v___y_5493_,
    );
    leanh::lean_dec(v___y_5493_);
    leanh::lean_dec_ref(v___y_5492_);
    leanh::lean_dec(v___y_5491_);
    leanh::lean_dec_ref(v___y_5490_);
    leanh::lean_dec_ref(v___y_5489_);
    return v_res_5496_;
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo___lam__1(
    mut v_info_5497_: *mut leanh::LeanObject,
    mut v___f_5498_: *mut leanh::LeanObject,
    mut v___y_5499_: *mut leanh::LeanObject,
    mut v___y_5500_: *mut leanh::LeanObject,
    mut v___y_5501_: *mut leanh::LeanObject,
    mut v___y_5502_: *mut leanh::LeanObject,
    mut v___y_5503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_info_5497_) {
        1 => {
            let mut v_i_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_5505_ = leanh::lean_ctor_get(v_info_5497_, 0);
            leanh::lean_inc_ref(v_i_5505_);
            leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5506_ = l_Lean_Server_locationLinksFromTermInfo(
                v_i_5505_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if leanh::lean_obj_tag(v___x_5506_) == 0 {
                let mut v_a_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_5507_ = leanh::lean_ctor_get(v___x_5506_, 0);
                leanh::lean_inc(v_a_5507_);
                leanh::lean_dec_ref_known(v___x_5506_, 1);
                leanh::lean_inc(v___y_5503_);
                leanh::lean_inc_ref(v___y_5502_);
                leanh::lean_inc(v___y_5501_);
                leanh::lean_inc_ref(v___y_5500_);
                leanh::lean_inc_ref(v___y_5499_);
                v___x_5508_ = leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5507_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    leanh::lean_box(0),
                );
                return v___x_5508_;
            } else {
                leanh::lean_dec_ref(v___f_5498_);
                return v___x_5506_;
            }
        }
        13 => {
            let mut v_i_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_5509_ = leanh::lean_ctor_get(v_info_5497_, 0);
            leanh::lean_inc_ref(v_i_5509_);
            leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5510_ = l_Lean_Server_locationLinksFromDelabTermInfo(
                v_i_5509_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if leanh::lean_obj_tag(v___x_5510_) == 0 {
                let mut v_a_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_5511_ = leanh::lean_ctor_get(v___x_5510_, 0);
                leanh::lean_inc(v_a_5511_);
                leanh::lean_dec_ref_known(v___x_5510_, 1);
                leanh::lean_inc(v___y_5503_);
                leanh::lean_inc_ref(v___y_5502_);
                leanh::lean_inc(v___y_5501_);
                leanh::lean_inc_ref(v___y_5500_);
                leanh::lean_inc_ref(v___y_5499_);
                v___x_5512_ = leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5511_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    leanh::lean_box(0),
                );
                return v___x_5512_;
            } else {
                leanh::lean_dec_ref(v___f_5498_);
                return v___x_5510_;
            }
        }
        7 => {
            let mut v_i_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_5513_ = leanh::lean_ctor_get(v_info_5497_, 0);
            leanh::lean_inc_ref(v_i_5513_);
            leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5514_ = l_Lean_Server_locationLinksFromFieldInfo(
                v_i_5513_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if leanh::lean_obj_tag(v___x_5514_) == 0 {
                let mut v_a_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_5515_ = leanh::lean_ctor_get(v___x_5514_, 0);
                leanh::lean_inc(v_a_5515_);
                leanh::lean_dec_ref_known(v___x_5514_, 1);
                leanh::lean_inc(v___y_5503_);
                leanh::lean_inc_ref(v___y_5502_);
                leanh::lean_inc(v___y_5501_);
                leanh::lean_inc_ref(v___y_5500_);
                leanh::lean_inc_ref(v___y_5499_);
                v___x_5516_ = leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5515_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    leanh::lean_box(0),
                );
                return v___x_5516_;
            } else {
                leanh::lean_dec_ref(v___f_5498_);
                return v___x_5514_;
            }
        }
        5 => {
            let mut v_i_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_5517_ = leanh::lean_ctor_get(v_info_5497_, 0);
            leanh::lean_inc_ref(v_i_5517_);
            leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5518_ = l_Lean_Server_locationLinksFromOptionInfo(
                v_i_5517_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if leanh::lean_obj_tag(v___x_5518_) == 0 {
                let mut v_a_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_5519_ = leanh::lean_ctor_get(v___x_5518_, 0);
                leanh::lean_inc(v_a_5519_);
                leanh::lean_dec_ref_known(v___x_5518_, 1);
                leanh::lean_inc(v___y_5503_);
                leanh::lean_inc_ref(v___y_5502_);
                leanh::lean_inc(v___y_5501_);
                leanh::lean_inc_ref(v___y_5500_);
                leanh::lean_inc_ref(v___y_5499_);
                v___x_5520_ = leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5519_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    leanh::lean_box(0),
                );
                return v___x_5520_;
            } else {
                leanh::lean_dec_ref(v___f_5498_);
                return v___x_5518_;
            }
        }
        3 => {
            let mut v_i_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_5521_ = leanh::lean_ctor_get(v_info_5497_, 0);
            leanh::lean_inc_ref(v_i_5521_);
            leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5522_ = l_Lean_Server_locationLinksFromCommandInfo___redArg(
                v_i_5521_,
                v___y_5499_,
                v___y_5502_,
            );
            if leanh::lean_obj_tag(v___x_5522_) == 0 {
                let mut v_a_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_5523_ = leanh::lean_ctor_get(v___x_5522_, 0);
                leanh::lean_inc(v_a_5523_);
                leanh::lean_dec_ref_known(v___x_5522_, 1);
                leanh::lean_inc(v___y_5503_);
                leanh::lean_inc_ref(v___y_5502_);
                leanh::lean_inc(v___y_5501_);
                leanh::lean_inc_ref(v___y_5500_);
                leanh::lean_inc_ref(v___y_5499_);
                v___x_5524_ = leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5523_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    leanh::lean_box(0),
                );
                return v___x_5524_;
            } else {
                leanh::lean_dec_ref(v___f_5498_);
                return v___x_5522_;
            }
        }
        6 => {
            let mut v_i_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_5525_ = leanh::lean_ctor_get(v_info_5497_, 0);
            leanh::lean_inc_ref(v_i_5525_);
            leanh::lean_dec_ref_known(v_info_5497_, 1);
            v___x_5526_ = l_Lean_Server_locationLinksFromErrorNameInfo(
                v_i_5525_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            leanh::lean_dec_ref(v_i_5525_);
            if leanh::lean_obj_tag(v___x_5526_) == 0 {
                let mut v_a_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_5527_ = leanh::lean_ctor_get(v___x_5526_, 0);
                leanh::lean_inc(v_a_5527_);
                leanh::lean_dec_ref_known(v___x_5526_, 1);
                leanh::lean_inc(v___y_5503_);
                leanh::lean_inc_ref(v___y_5502_);
                leanh::lean_inc(v___y_5501_);
                leanh::lean_inc_ref(v___y_5500_);
                leanh::lean_inc_ref(v___y_5499_);
                v___x_5528_ = leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5527_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    leanh::lean_box(0),
                );
                return v___x_5528_;
            } else {
                leanh::lean_dec_ref(v___f_5498_);
                return v___x_5526_;
            }
        }
        16 => {
            let mut v_i_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_5529_ = leanh::lean_ctor_get(v_info_5497_, 0);
            leanh::lean_inc_ref(v_i_5529_);
            leanh::lean_dec_ref_known(v_info_5497_, 1);
            v_name_5530_ = leanh::lean_ctor_get(v_i_5529_, 1);
            leanh::lean_inc(v_name_5530_);
            leanh::lean_dec_ref(v_i_5529_);
            v___x_5531_ = l_Lean_Server_locationLinksFromDecl(
                v_name_5530_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
            );
            if leanh::lean_obj_tag(v___x_5531_) == 0 {
                let mut v_a_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_5532_ = leanh::lean_ctor_get(v___x_5531_, 0);
                leanh::lean_inc(v_a_5532_);
                leanh::lean_dec_ref_known(v___x_5531_, 1);
                leanh::lean_inc(v___y_5503_);
                leanh::lean_inc_ref(v___y_5502_);
                leanh::lean_inc(v___y_5501_);
                leanh::lean_inc_ref(v___y_5500_);
                leanh::lean_inc_ref(v___y_5499_);
                v___x_5533_ = leanh::lean_apply_7(
                    v___f_5498_,
                    v_a_5532_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                    v___y_5503_,
                    leanh::lean_box(0),
                );
                return v___x_5533_;
            } else {
                leanh::lean_dec_ref(v___f_5498_);
                return v___x_5531_;
            }
        }
        _ => {
            let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_info_5497_);
            v___x_5534_ = l_Lean_Server_locationLinksFromDecl___closed__0;
            leanh::lean_inc(v___y_5503_);
            leanh::lean_inc_ref(v___y_5502_);
            leanh::lean_inc(v___y_5501_);
            leanh::lean_inc_ref(v___y_5500_);
            leanh::lean_inc_ref(v___y_5499_);
            v___x_5535_ = leanh::lean_apply_7(
                v___f_5498_,
                v___x_5534_,
                v___y_5499_,
                v___y_5500_,
                v___y_5501_,
                v___y_5502_,
                v___y_5503_,
                leanh::lean_box(0),
            );
            return v___x_5535_;
        }
    }
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo___lam__1___boxed(
    mut v_info_5536_: *mut leanh::LeanObject,
    mut v___f_5537_: *mut leanh::LeanObject,
    mut v___y_5538_: *mut leanh::LeanObject,
    mut v___y_5539_: *mut leanh::LeanObject,
    mut v___y_5540_: *mut leanh::LeanObject,
    mut v___y_5541_: *mut leanh::LeanObject,
    mut v___y_5542_: *mut leanh::LeanObject,
    mut v___y_5543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5544_ = l_Lean_Server_locationLinksOfInfo___lam__1(
        v_info_5536_,
        v___f_5537_,
        v___y_5538_,
        v___y_5539_,
        v___y_5540_,
        v___y_5541_,
        v___y_5542_,
    );
    leanh::lean_dec(v___y_5542_);
    leanh::lean_dec_ref(v___y_5541_);
    leanh::lean_dec(v___y_5540_);
    leanh::lean_dec_ref(v___y_5539_);
    leanh::lean_dec_ref(v___y_5538_);
    return v_res_5544_;
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo(
    mut v_doc_5545_: *mut leanh::LeanObject,
    mut v_kind_5546_: u8,
    mut v_ictx_5547_: *mut leanh::LeanObject,
    mut v_infoTree_x3f_5548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ctx_5550_ = leanh::lean_ctor_get(v_ictx_5547_, 0);
    leanh::lean_inc_ref(v_ctx_5550_);
    v_info_5551_ = leanh::lean_ctor_get(v_ictx_5547_, 1);
    leanh::lean_inc_ref_n(v_info_5551_, 3);
    v_children_5552_ = leanh::lean_ctor_get(v_ictx_5547_, 2);
    leanh::lean_inc_ref(v_children_5552_);
    leanh::lean_dec_ref(v_ictx_5547_);
    v___x_5553_ = leanh::lean_box((v_kind_5546_) as usize);
    v___f_5554_ = leanh::lean_alloc_closure(
        l_Lean_Server_locationLinksOfInfo___lam__0___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    leanh::lean_closure_set(v___f_5554_, 0, v___x_5553_);
    v___y_5555_ = leanh::lean_alloc_closure(
        l_Lean_Server_locationLinksOfInfo___lam__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    leanh::lean_closure_set(v___y_5555_, 0, v_info_5551_);
    leanh::lean_closure_set(v___y_5555_, 1, v___f_5554_);
    v___x_5556_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5556_, 0, v_info_5551_);
    v_ctx_5557_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
    leanh::lean_ctor_set(v_ctx_5557_, 0, v_doc_5545_);
    leanh::lean_ctor_set(v_ctx_5557_, 1, v_infoTree_x3f_5548_);
    leanh::lean_ctor_set(v_ctx_5557_, 2, v___x_5556_);
    leanh::lean_ctor_set(v_ctx_5557_, 3, v_children_5552_);
    leanh::lean_ctor_set_uint8(
        v_ctx_5557_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v_kind_5546_,
    );
    v___x_5558_ = l_Lean_Elab_Info_lctx(v_info_5551_);
    leanh::lean_dec_ref(v_info_5551_);
    v___x_5559_ =
        l_Lean_Server_GoToM_run___redArg(v_ctx_5557_, v_ctx_5550_, v___x_5558_, v___y_5555_);
    return v___x_5559_;
}
pub unsafe fn l_Lean_Server_locationLinksOfInfo___boxed(
    mut v_doc_5560_: *mut leanh::LeanObject,
    mut v_kind_5561_: *mut leanh::LeanObject,
    mut v_ictx_5562_: *mut leanh::LeanObject,
    mut v_infoTree_x3f_5563_: *mut leanh::LeanObject,
    mut v_a_5564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_5565_: u8 = 0;
    let mut v_res_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5565_ = (leanh::lean_unbox(v_kind_5561_) as u8);
    v_res_5566_ = l_Lean_Server_locationLinksOfInfo(
        v_doc_5560_,
        v_kind_boxed_5565_,
        v_ictx_5562_,
        v_infoTree_x3f_5563_,
    );
    return v_res_5566_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_GoTo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Utils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Internal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_GoTo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_GoTo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Utils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Internal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_GoTo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_GoTo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_GoTo(builtin);
}