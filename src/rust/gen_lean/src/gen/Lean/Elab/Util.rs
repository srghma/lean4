// Lean compiler output
// Module: Lean.Elab.Util
// Imports: Lean.Parser.Extension Lean.Parser.Command Lean.KeyedDeclsAttribute Lean.BuiltinDocAttr Lean.ExtraModUses Init.Prelude
use crate::r#gen::Init::Control::Except::l_liftExcept___redArg;
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Format::Instances::l_String_toFormat;
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::Control::{
    l_List_forIn_x27_loop___redArg, l_List_forM___redArg,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_Syntax_unsetTrailing, l_Lean_evalPrio,
    lean_name_append_index_after,
};
use crate::r#gen::Init::Prelude::{
    initialize_Init_Prelude, l_EStateM_bind, l_EStateM_instMonad___lam__0,
    l_EStateM_instMonad___lam__1, l_EStateM_instMonad___lam__2,
    l_EStateM_instMonadExceptOfOfBacktrackable___redArg, l_EStateM_map, l_EStateM_nonBacktrackable,
    l_EStateM_pure, l_EStateM_seqRight, l_Lean_Macro_getCurrNamespace, l_Lean_Macro_hasDecl,
    l_Lean_Macro_throwUnsupported___redArg, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_Syntax_getArg, l_Lean_Syntax_getKind,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_mkAtom, l_Lean_replaceRef,
    l_List_foldl___at___00Lean_MacroScopesView_review_spec__0, l_List_foldl___redArg,
    l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
    l_ReaderT_instMonadExceptOf___redArg___lam__2, l_ReaderT_pure___boxed,
    runtime_initialize_Init_Prelude,
};
use crate::r#gen::Lean::Attributes::l_Lean_Attribute_Builtin_getId;
use crate::r#gen::Lean::BuiltinDocAttr::{
    initialize_Lean_BuiltinDocAttr, l_Lean_declareBuiltinDocStringAndRanges,
    runtime_initialize_Lean_BuiltinDocAttr,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::KVMap::l_Lean_KVMap_instValueBool;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::{
    l_Lean_Option_get___redArg, l_Lean_Options_empty, lean_register_option,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::Exception::{
    l_Lean_Elab_isAbortExceptionId, l_Lean_Elab_throwUnsupportedSyntax___redArg,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_evalConstCheck___redArg,
    l_Lean_Environment_findConstVal_x3f, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_getRef, l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData,
    l_Lean_throwError___redArg, l_Lean_throwErrorAt___redArg, l_Lean_throwMaxRecDepthAt___redArg,
    l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::ExtraModUses::{
    initialize_Lean_ExtraModUses, l___private_Lean_ExtraModUses_0__Lean_extraModUses,
    l_Lean_indirectModUseExt, l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
    l_Lean_recordExtraModUseFromDecl___redArg, runtime_initialize_Lean_ExtraModUses,
};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_InternalExceptionId_getName___boxed;
use crate::r#gen::Lean::KeyedDeclsAttribute::{
    initialize_Lean_KeyedDeclsAttribute, l_Lean_KeyedDeclsAttribute_getEntries___redArg,
    l_Lean_KeyedDeclsAttribute_init___redArg, runtime_initialize_Lean_KeyedDeclsAttribute,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_empty;
use crate::r#gen::Lean::Log::{
    l_Lean_getRefPos___redArg, l_Lean_logError___redArg, l_Lean_logErrorAt___redArg,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData, l_Lean_toMessageList,
};
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::Parser::Extension::{
    initialize_Lean_Parser_Extension, l_Lean_Parser_isValidSyntaxNodeKind,
    runtime_initialize_Lean_Parser_Extension,
};
use crate::r#gen::Lean::PrivateName::{l_Lean_isPrivateName, l_Lean_privateToUserName};
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_reprint;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_addTrace___redArg,
    l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_string_dec_eq, lean_uint64_of_nat,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_Elab_expandOptNamedPrio___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_expandOptNamedPrio___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_expandOptNamedPrio___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_expandOptNamedPrio___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_expandOptNamedPrio___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_expandOptNamedPrio___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_expandOptNamedPrio___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 97, 109, 101, 100, 80, 114, 105, 111, 0],
    };
static mut l_Lean_Elab_expandOptNamedPrio___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__2_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_expandOptNamedPrio___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__3_value)
                as *mut crate::leanh::LeanObject,
            13348752267415789739 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_expandOptNamedPrio___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 99, 114, 111, 83, 116, 97, 99, 107, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6746591144584426489 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,1314940330429522239 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [100, 105, 115, 112, 108, 97, 121, 32, 109, 97, 99, 114, 111, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 32, 115, 116, 97, 99, 107, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8636882522227397730 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9662849064889376504 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_pp_macroStack: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0_value:
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
        119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2_value:
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
        119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97,
        110, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0_value:
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
    m_data: [102, 97, 105, 108, 101, 100, 0],
};
static mut l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0_value: crate::leanh::LeanStringObject<
    27,
> = crate::leanh::LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101,
        32, 107, 105, 110, 100, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0_value:
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
    m_data: [83, 121, 110, 116, 97, 120, 0],
};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0_value) as *mut crate::leanh::LeanObject,5337926038336999469 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__1_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__3_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__4_value: crate::leanh::LeanStringObject<
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
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__4_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__6_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__7_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__8_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        14997215300048349804 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__12_value:
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__13_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__12_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__13_value)
            as *mut crate::leanh::LeanObject,
        7677164612348466033 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__15_value:
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
    m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_mkElabAttribute___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___redArg___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_mkElabAttribute___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkElabAttribute___redArg___closed__1_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 0],
};
static mut l_Lean_Elab_mkElabAttribute___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__0_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        98, 117, 105, 108, 116, 105, 110, 95, 109, 97, 99, 114, 111, 0,
    ],
};
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11704967964546086785 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__2_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [109, 97, 99, 114, 111, 0],
    };
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2_value)
                as *mut crate::leanh::LeanObject,
            89168197957061509 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__4_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [77, 97, 99, 114, 111, 0],
    };
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__4_value)
                as *mut crate::leanh::LeanObject,
            18105168627502861736 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [109, 97, 99, 114, 111, 65, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9634981646868643031 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_macroAttribute: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0_value: crate::leanh::LeanStringObject<391> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 391, m_capacity: 391, m_length: 388, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 32, 109, 97, 99, 114, 111, 32, 101, 120, 112, 97, 110, 100, 101, 114, 32, 102, 111, 114, 32, 97, 32, 103, 105, 118, 101, 110, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 46, 10, 10, 65, 32, 109, 97, 99, 114, 111, 32, 101, 120, 112, 97, 110, 100, 101, 114, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 32, 96, 76, 101, 97, 110, 46, 77, 97, 99, 114, 111, 96, 32, 40, 119, 104, 105, 99, 104, 32, 105, 115, 32, 96, 76, 101, 97, 110, 46, 83, 121, 110, 116, 97, 120, 32, 226, 134, 146, 32, 76, 101, 97, 110, 46, 77, 97, 99, 114, 111, 77, 32, 76, 101, 97, 110, 46, 83, 121, 110, 116, 97, 120, 96, 41, 44, 10, 105, 46, 101, 46, 32, 115, 104, 111, 117, 108, 100, 32, 116, 97, 107, 101, 32, 115, 121, 110, 116, 97, 120, 32, 111, 102, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 32, 97, 115, 32, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 97, 110, 100, 32, 112, 114, 111, 100, 117, 99, 101, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 115, 121, 110, 116, 97, 120, 10, 105, 110, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 115, 121, 110, 116, 97, 120, 32, 99, 97, 116, 101, 103, 111, 114, 121, 46, 10, 10, 84, 104, 101, 32, 96, 109, 97, 99, 114, 111, 95, 114, 117, 108, 101, 115, 96, 32, 97, 110, 100, 32, 96, 109, 97, 99, 114, 111, 96, 32, 99, 111, 109, 109, 97, 110, 100, 115, 32, 115, 104, 111, 117, 108, 100, 32, 117, 115, 117, 97, 108, 108, 121, 32, 98, 101, 32, 112, 114, 101, 102, 101, 114, 114, 101, 100, 32, 111, 118, 101, 114, 32, 117, 115, 105, 110, 103, 32, 116, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 10, 100, 105, 114, 101, 99, 116, 108, 121, 46, 10, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 139 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 150 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 91 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 91 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 150 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 150 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0_value:
    crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 158,
    m_capacity: 158,
    m_length: 157,
    m_data: [
        109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100,
        101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104,
        101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32,
        109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116,
        111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115,
        101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110,
        111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116,
        32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97,
        116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_EStateM_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_EStateM_instMonad___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_EStateM_instMonad___lam__2 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__3_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_map as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__5_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_pure as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__6_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_seqRight as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__7_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__8_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_bind as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_liftMacroM___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_liftMacroM___redArg___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_liftMacroM___redArg___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_liftMacroM___redArg___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_liftMacroM___redArg___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___redArg___closed__15_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ReaderT_pure___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_logException___redArg___lam__0___closed__0_value:
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
        105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 58,
        32, 0,
    ],
};
static mut l_Lean_Elab_logException___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_logException___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_logException___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_logException___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0_value:
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
    m_data: [58, 0],
};
static mut l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0_value:
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
    m_data: [44, 32, 101, 114, 114, 111, 114, 115, 32, 0],
};
static mut l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13803056972440293078 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2082380159358162175 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut crate::leanh::LeanObject,5163195698633565746 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3797997157859537744 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,349153818491263805 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8303187326548929696 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut crate::leanh::LeanObject,4832156502452437593 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11911250769714989207 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1771634189876703749 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2034298159 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,18033771262542104897 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5059639781667360386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6203526536341765518 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10631922230448659167 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 101, 112, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16279398898093714393 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 115, 117, 108, 116, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16279398898093714393 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4251351871078927870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Syntax_prettyPrint(
    mut v_stx_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_stx_3067_);
    v___x_3068_ = l_Lean_Syntax_unsetTrailing(v_stx_3067_);
    v___x_3069_ = l_Lean_Syntax_reprint(v___x_3068_);
    if crate::leanh::lean_obj_tag(v___x_3069_) == 0 {
        let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3071_: u8 = 0;
        let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3070_ = crate::leanh::lean_box(0);
        v___x_3071_ = 0;
        v___x_3072_ = l_Lean_Syntax_formatStx(v_stx_3067_, v___x_3070_, v___x_3071_);
        return v___x_3072_;
    } else {
        let mut v_val_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_3067_);
        v_val_3073_ = crate::leanh::lean_ctor_get(v___x_3069_, 0);
        crate::leanh::lean_inc(v_val_3073_);
        crate::leanh::lean_dec_ref_known(v___x_3069_, 1);
        v___x_3074_ = l_String_toFormat(v_val_3073_);
        return v___x_3074_;
    }
}
pub unsafe fn l_Lean_MacroScopesView_format(
    mut v_view_3075_: *mut crate::leanh::LeanObject,
    mut v_mainModule_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: u8 = 0;
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3082_ = crate::leanh::lean_ctor_get(v_view_3075_, 0);
                crate::leanh::lean_inc(v_name_3082_);
                v_imported_3083_ = crate::leanh::lean_ctor_get(v_view_3075_, 1);
                crate::leanh::lean_inc(v_imported_3083_);
                v_ctx_3084_ = crate::leanh::lean_ctor_get(v_view_3075_, 2);
                crate::leanh::lean_inc(v_ctx_3084_);
                v_scopes_3085_ = crate::leanh::lean_ctor_get(v_view_3075_, 3);
                crate::leanh::lean_inc(v_scopes_3085_);
                crate::leanh::lean_dec_ref(v_view_3075_);
                v___x_3086_ = l_List_isEmpty___redArg(v_scopes_3085_);
                if v___x_3086_ == 0 {
                    v___x_3087_ = lean_name_eq(v_ctx_3084_, v_mainModule_3076_);
                    if v___x_3087_ == 0 {
                        v___x_3088_ = l_Lean_Name_append(v_name_3082_, v_imported_3083_);
                        v___x_3089_ = l_Lean_Name_append(v___x_3088_, v_ctx_3084_);
                        v___x_3090_ = l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(
                            v___x_3089_,
                            v_scopes_3085_,
                        );
                        v___y_3078_ = v___x_3090_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_ctx_3084_);
                        v___x_3091_ = l_Lean_Name_append(v_name_3082_, v_imported_3083_);
                        v___x_3092_ = l_List_foldl___at___00Lean_MacroScopesView_review_spec__0(
                            v___x_3091_,
                            v_scopes_3085_,
                        );
                        v___y_3078_ = v___x_3092_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_scopes_3085_);
                    crate::leanh::lean_dec(v_ctx_3084_);
                    crate::leanh::lean_dec(v_imported_3083_);
                    v___y_3078_ = v_name_3082_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3079_ = 1;
                v___x_3080_ = l_Lean_Name_toString(v___y_3078_, v___x_3079_);
                v___x_3081_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3081_, 0, v___x_3080_);
                return v___x_3081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MacroScopesView_format___boxed(
    mut v_view_3093_: *mut crate::leanh::LeanObject,
    mut v_mainModule_3094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3095_ = l_Lean_MacroScopesView_format(v_view_3093_, v_mainModule_3094_);
    crate::leanh::lean_dec(v_mainModule_3094_);
    return v_res_3095_;
}
pub unsafe fn l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(
    mut v_x_3096_: *mut crate::leanh::LeanObject,
    mut v_x_3097_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: u8 = 0;
    let mut v_head_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3096_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_3097_) == 0 {
                        v___x_3098_ = 1;
                        return v___x_3098_;
                    } else {
                        v___x_3099_ = 0;
                        return v___x_3099_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_3097_) == 0 {
                        v___x_3100_ = 0;
                        return v___x_3100_;
                    } else {
                        v_head_3101_ = crate::leanh::lean_ctor_get(v_x_3096_, 0);
                        v_tail_3102_ = crate::leanh::lean_ctor_get(v_x_3096_, 1);
                        v_head_3103_ = crate::leanh::lean_ctor_get(v_x_3097_, 0);
                        v_tail_3104_ = crate::leanh::lean_ctor_get(v_x_3097_, 1);
                        v___x_3105_ = lean_nat_dec_eq(v_head_3101_, v_head_3103_);
                        if v___x_3105_ == 0 {
                            return v___x_3105_;
                        } else {
                            v_x_3096_ = v_tail_3102_;
                            v_x_3097_ = v_tail_3104_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0___boxed(
    mut v_x_3107_: *mut crate::leanh::LeanObject,
    mut v_x_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3109_: u8 = 0;
    let mut v_r_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3109_ = l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(v_x_3107_, v_x_3108_);
    crate::leanh::lean_dec(v_x_3108_);
    crate::leanh::lean_dec(v_x_3107_);
    v_r_3110_ = crate::leanh::lean_box((v_res_3109_) as usize);
    return v_r_3110_;
}
pub unsafe fn l_Lean_MacroScopesView_equalScope(
    mut v_a_3111_: *mut crate::leanh::LeanObject,
    mut v_b_3112_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_imported_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_imported_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3120_: u8 = 0;
    let mut v___x_3121_: u8 = 0;
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imported_3113_ = crate::leanh::lean_ctor_get(v_a_3111_, 1);
                v_ctx_3114_ = crate::leanh::lean_ctor_get(v_a_3111_, 2);
                v_scopes_3115_ = crate::leanh::lean_ctor_get(v_a_3111_, 3);
                v_imported_3116_ = crate::leanh::lean_ctor_get(v_b_3112_, 1);
                v_ctx_3117_ = crate::leanh::lean_ctor_get(v_b_3112_, 2);
                v_scopes_3118_ = crate::leanh::lean_ctor_get(v_b_3112_, 3);
                v___x_3122_ = l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(
                    v_scopes_3115_,
                    v_scopes_3118_,
                );
                if v___x_3122_ == 0 {
                    v___y_3120_ = v___x_3122_;
                    state = 1;
                    continue;
                } else {
                    v___x_3123_ = lean_name_eq(v_ctx_3114_, v_ctx_3117_);
                    v___y_3120_ = v___x_3123_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3120_ == 0 {
                    return v___y_3120_;
                } else {
                    v___x_3121_ = lean_name_eq(v_imported_3113_, v_imported_3116_);
                    return v___x_3121_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MacroScopesView_equalScope___boxed(
    mut v_a_3124_: *mut crate::leanh::LeanObject,
    mut v_b_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3126_: u8 = 0;
    let mut v_r_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3126_ = l_Lean_MacroScopesView_equalScope(v_a_3124_, v_b_3125_);
    crate::leanh::lean_dec_ref(v_b_3125_);
    crate::leanh::lean_dec_ref(v_a_3124_);
    v_r_3127_ = crate::leanh::lean_box((v_res_3126_) as usize);
    return v_r_3127_;
}
pub unsafe fn l_Lean_Elab_expandOptNamedPrio(
    mut v_stx_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3140_: u8 = 0;
    v___x_3140_ = l_Lean_Syntax_isNone(v_stx_3137_);
    if v___x_3140_ == 0 {
        let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3144_: u8 = 0;
        v___x_3141_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3142_ = l_Lean_Syntax_getArg(v_stx_3137_, v___x_3141_);
        v___x_3143_ = l_Lean_Elab_expandOptNamedPrio___closed__4;
        crate::leanh::lean_inc(v___x_3142_);
        v___x_3144_ = l_Lean_Syntax_isOfKind(v___x_3142_, v___x_3143_);
        if v___x_3144_ == 0 {
            let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_3142_);
            v___x_3145_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3139_);
            return v___x_3145_;
        } else {
            let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3146_ = crate::leanh::lean_unsigned_to_nat(3);
            v___x_3147_ = l_Lean_Syntax_getArg(v___x_3142_, v___x_3146_);
            crate::leanh::lean_dec(v___x_3142_);
            v___x_3148_ = l_Lean_evalPrio(v___x_3147_, v_a_3138_, v_a_3139_);
            return v___x_3148_;
        }
    } else {
        let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3149_ = crate::leanh::lean_unsigned_to_nat(1000);
        v___x_3150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3150_, 0, v___x_3149_);
        crate::leanh::lean_ctor_set(v___x_3150_, 1, v_a_3139_);
        return v___x_3150_;
    }
}
pub unsafe fn l_Lean_Elab_expandOptNamedPrio___boxed(
    mut v_stx_3151_: *mut crate::leanh::LeanObject,
    mut v_a_3152_: *mut crate::leanh::LeanObject,
    mut v_a_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3154_ = l_Lean_Elab_expandOptNamedPrio(v_stx_3151_, v_a_3152_, v_a_3153_);
    crate::leanh::lean_dec_ref(v_a_3152_);
    crate::leanh::lean_dec(v_stx_3151_);
    return v_res_3154_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(
    mut v_x_3155_: *mut crate::leanh::LeanObject,
    mut v_x_3156_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3155_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_3156_) == 0 {
            let mut v___x_3157_: u8 = 0;
            v___x_3157_ = 1;
            return v___x_3157_;
        } else {
            let mut v___x_3158_: u8 = 0;
            v___x_3158_ = 0;
            return v___x_3158_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_3156_) == 0 {
            let mut v___x_3159_: u8 = 0;
            v___x_3159_ = 0;
            return v___x_3159_;
        } else {
            let mut v_val_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3162_: u8 = 0;
            v_val_3160_ = crate::leanh::lean_ctor_get(v_x_3155_, 0);
            v_val_3161_ = crate::leanh::lean_ctor_get(v_x_3156_, 0);
            v___x_3162_ = lean_nat_dec_eq(v_val_3160_, v_val_3161_);
            return v___x_3162_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0___boxed(
    mut v_x_3163_: *mut crate::leanh::LeanObject,
    mut v_x_3164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3165_: u8 = 0;
    let mut v_r_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3165_ =
        l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(v_x_3163_, v_x_3164_);
    crate::leanh::lean_dec(v_x_3164_);
    crate::leanh::lean_dec(v_x_3163_);
    v_r_3166_ = crate::leanh::lean_box((v_res_3165_) as usize);
    return v_r_3166_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(
    mut v___x_3167_: *mut crate::leanh::LeanObject,
    mut v_x_3168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_before_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3168_) == 0 {
                    v___x_3169_ = crate::leanh::lean_box(0);
                    return v___x_3169_;
                } else {
                    v_head_3170_ = crate::leanh::lean_ctor_get(v_x_3168_, 0);
                    v_tail_3171_ = crate::leanh::lean_ctor_get(v_x_3168_, 1);
                    v_before_3172_ = crate::leanh::lean_ctor_get(v_head_3170_, 0);
                    v___x_3173_ = 0;
                    v___x_3174_ = l_Lean_Syntax_getPos_x3f(v_before_3172_, v___x_3173_);
                    v___x_3175_ = l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(
                        v___x_3174_,
                        v___x_3167_,
                    );
                    crate::leanh::lean_dec(v___x_3174_);
                    if v___x_3175_ == 0 {
                        crate::leanh::lean_inc(v_head_3170_);
                        v___x_3176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3176_, 0, v_head_3170_);
                        return v___x_3176_;
                    } else {
                        v_x_3168_ = v_tail_3171_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1___boxed(
    mut v___x_3178_: *mut crate::leanh::LeanObject,
    mut v_x_3179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3180_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_3178_, v_x_3179_);
    crate::leanh::lean_dec(v_x_3179_);
    crate::leanh::lean_dec(v___x_3178_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_Elab_getBetterRef(
    mut v_ref_3181_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3183_: u8 = 0;
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3183_ = 0;
    v___x_3184_ = l_Lean_Syntax_getPos_x3f(v_ref_3181_, v___x_3183_);
    if crate::leanh::lean_obj_tag(v___x_3184_) == 0 {
        let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3185_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(
            v___x_3184_,
            v_macroStack_3182_,
        );
        if crate::leanh::lean_obj_tag(v___x_3185_) == 0 {
            crate::leanh::lean_inc(v_ref_3181_);
            return v_ref_3181_;
        } else {
            let mut v_val_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_before_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_3186_ = crate::leanh::lean_ctor_get(v___x_3185_, 0);
            crate::leanh::lean_inc(v_val_3186_);
            crate::leanh::lean_dec_ref_known(v___x_3185_, 1);
            v_before_3187_ = crate::leanh::lean_ctor_get(v_val_3186_, 0);
            crate::leanh::lean_inc(v_before_3187_);
            crate::leanh::lean_dec(v_val_3186_);
            return v_before_3187_;
        }
    } else {
        crate::leanh::lean_dec_ref_known(v___x_3184_, 1);
        crate::leanh::lean_inc(v_ref_3181_);
        return v_ref_3181_;
    }
}
pub unsafe fn l_Lean_Elab_getBetterRef___boxed(
    mut v_ref_3188_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3190_ = l_Lean_Elab_getBetterRef(v_ref_3188_, v_macroStack_3189_);
    crate::leanh::lean_dec(v_macroStack_3189_);
    crate::leanh::lean_dec(v_ref_3188_);
    return v_res_3190_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(
    mut v_name_3191_: *mut crate::leanh::LeanObject,
    mut v_decl_3192_: *mut crate::leanh::LeanObject,
    mut v_ref_3193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut v_unused_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3214_: u8 = 0;
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3195_ = crate::leanh::lean_ctor_get(v_decl_3192_, 0);
                v_descr_3196_ = crate::leanh::lean_ctor_get(v_decl_3192_, 1);
                v_deprecation_x3f_3197_ = crate::leanh::lean_ctor_get(v_decl_3192_, 2);
                v___x_3198_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3199_ = (crate::leanh::lean_unbox(v_defValue_3195_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_3198_, 0 as u32, v___x_3199_);
                crate::leanh::lean_inc(v_deprecation_x3f_3197_);
                crate::leanh::lean_inc_ref(v_descr_3196_);
                crate::leanh::lean_inc_n(v_name_3191_, 2);
                v___x_3200_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3200_, 0, v_name_3191_);
                crate::leanh::lean_ctor_set(v___x_3200_, 1, v_ref_3193_);
                crate::leanh::lean_ctor_set(v___x_3200_, 2, v___x_3198_);
                crate::leanh::lean_ctor_set(v___x_3200_, 3, v_descr_3196_);
                crate::leanh::lean_ctor_set(v___x_3200_, 4, v_deprecation_x3f_3197_);
                v___x_3201_ = lean_register_option(v_name_3191_, v___x_3200_);
                if crate::leanh::lean_obj_tag(v___x_3201_) == 0 {
                    v_isSharedCheck_3209_ = (!crate::leanh::lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3209_ == 0 {
                        v_unused_3210_ = crate::leanh::lean_ctor_get(v___x_3201_, 0);
                        crate::leanh::lean_dec(v_unused_3210_);
                        v___x_3203_ = v___x_3201_;
                        v_isShared_3204_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3201_);
                        v___x_3203_ = crate::leanh::lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_3191_);
                    v_a_3211_ = crate::leanh::lean_ctor_get(v___x_3201_, 0);
                    v_isSharedCheck_3218_ = (!crate::leanh::lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3218_ == 0 {
                        v___x_3213_ = v___x_3201_;
                        v_isShared_3214_ = v_isSharedCheck_3218_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3211_);
                        crate::leanh::lean_dec(v___x_3201_);
                        v___x_3213_ = crate::leanh::lean_box(0);
                        v_isShared_3214_ = v_isSharedCheck_3218_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_3195_);
                v___x_3205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3205_, 0, v_name_3191_);
                crate::leanh::lean_ctor_set(v___x_3205_, 1, v_defValue_3195_);
                if v_isShared_3204_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3203_, 0, v___x_3205_);
                    v___x_3207_ = v___x_3203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
                    v___x_3207_ = v_reuseFailAlloc_3208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3207_;
            }
            3 => {
                if v_isShared_3214_ == 0 {
                    v___x_3216_ = v___x_3213_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
                    v___x_3216_ = v_reuseFailAlloc_3217_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3219_: *mut crate::leanh::LeanObject,
    mut v_decl_3220_: *mut crate::leanh::LeanObject,
    mut v_ref_3221_: *mut crate::leanh::LeanObject,
    mut v_a_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v_name_3219_, v_decl_3220_, v_ref_3221_);
    crate::leanh::lean_dec_ref(v_decl_3220_);
    return v_res_3223_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3242_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_;
    v___x_3243_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_;
    v___x_3244_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_;
    v___x_3245_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v___x_3242_, v___x_3243_, v___x_3244_);
    return v___x_3245_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4____boxed(
    mut v_a_3246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3247_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
    return v_res_3247_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1;
    v___x_3252_ = l_Lean_MessageData_ofFormat(v___x_3251_);
    return v___x_3252_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___redArg___lam__0(
    mut v___x_3253_: *mut crate::leanh::LeanObject,
    mut v_msgData_3254_: *mut crate::leanh::LeanObject,
    mut v_elem_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_before_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut v_unused_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_before_3256_ = crate::leanh::lean_ctor_get(v_elem_3255_, 0);
                v_isSharedCheck_3268_ = (!crate::leanh::lean_is_exclusive(v_elem_3255_)) as u8;
                if v_isSharedCheck_3268_ == 0 {
                    v_unused_3269_ = crate::leanh::lean_ctor_get(v_elem_3255_, 1);
                    crate::leanh::lean_dec(v_unused_3269_);
                    v___x_3258_ = v_elem_3255_;
                    v_isShared_3259_ = v_isSharedCheck_3268_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_3256_);
                    crate::leanh::lean_dec(v_elem_3255_);
                    v___x_3258_ = crate::leanh::lean_box(0);
                    v_isShared_3259_ = v_isSharedCheck_3268_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3259_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3258_, 7);
                    crate::leanh::lean_ctor_set(v___x_3258_, 1, v___x_3253_);
                    crate::leanh::lean_ctor_set(v___x_3258_, 0, v_msgData_3254_);
                    v___x_3261_ = v___x_3258_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3267_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_msgData_3254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3267_, 1, v___x_3253_);
                    v___x_3261_ = v_reuseFailAlloc_3267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3262_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2,
                );
                v___x_3263_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3263_, 0, v___x_3261_);
                crate::leanh::lean_ctor_set(v___x_3263_, 1, v___x_3262_);
                v___x_3264_ = l_Lean_MessageData_ofSyntax(v_before_3256_);
                v___x_3265_ = l_Lean_indentD(v___x_3264_);
                v___x_3266_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3266_, 0, v___x_3263_);
                crate::leanh::lean_ctor_set(v___x_3266_, 1, v___x_3265_);
                return v___x_3266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3270_ = crate::leanh::lean_box(1);
    v___x_3271_ = l_Lean_MessageData_ofFormat(v___x_3270_);
    return v___x_3271_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3272_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once),
        _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0,
    );
    v___f_3273_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_addMacroStack___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3273_, 0, v___x_3272_);
    return v___f_3273_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3277_ = l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3;
    v___x_3278_ = l_Lean_MessageData_ofFormat(v___x_3277_);
    return v___x_3278_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___redArg___lam__1(
    mut v___x_3279_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3280_: *mut crate::leanh::LeanObject,
    mut v_msgData_3281_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3282_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v_toPure_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v_toPure_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3309_: u8 = 0;
    let mut v_unused_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3284_ = l_Lean_Elab_pp_macroStack;
                v___x_3285_ =
                    l_Lean_Option_get___redArg(v___x_3279_, v_____do__lift_3283_, v___x_3284_);
                v___x_3286_ = (crate::leanh::lean_unbox(v___x_3285_) as u8);
                crate::leanh::lean_dec(v___x_3285_);
                if v___x_3286_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_3282_);
                    v_toPure_3287_ = crate::leanh::lean_ctor_get(v_toApplicative_3280_, 1);
                    crate::leanh::lean_inc(v_toPure_3287_);
                    crate::leanh::lean_dec_ref(v_toApplicative_3280_);
                    v___x_3288_ = crate::leanh::lean_apply_2(
                        v_toPure_3287_,
                        crate::leanh::lean_box(0),
                        v_msgData_3281_,
                    );
                    return v___x_3288_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_3282_) == 0 {
                        v_toPure_3289_ = crate::leanh::lean_ctor_get(v_toApplicative_3280_, 1);
                        crate::leanh::lean_inc(v_toPure_3289_);
                        crate::leanh::lean_dec_ref(v_toApplicative_3280_);
                        v___x_3290_ = crate::leanh::lean_apply_2(
                            v_toPure_3289_,
                            crate::leanh::lean_box(0),
                            v_msgData_3281_,
                        );
                        return v___x_3290_;
                    } else {
                        v_head_3291_ = crate::leanh::lean_ctor_get(v_macroStack_3282_, 0);
                        crate::leanh::lean_inc(v_head_3291_);
                        v_after_3292_ = crate::leanh::lean_ctor_get(v_head_3291_, 1);
                        v_isSharedCheck_3309_ =
                            (!crate::leanh::lean_is_exclusive(v_head_3291_)) as u8;
                        if v_isSharedCheck_3309_ == 0 {
                            v_unused_3310_ = crate::leanh::lean_ctor_get(v_head_3291_, 0);
                            crate::leanh::lean_dec(v_unused_3310_);
                            v___x_3294_ = v_head_3291_;
                            v_isShared_3295_ = v_isSharedCheck_3309_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_3292_);
                            crate::leanh::lean_dec(v_head_3291_);
                            v___x_3294_ = crate::leanh::lean_box(0);
                            v_isShared_3295_ = v_isSharedCheck_3309_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_toPure_3296_ = crate::leanh::lean_ctor_get(v_toApplicative_3280_, 1);
                crate::leanh::lean_inc(v_toPure_3296_);
                crate::leanh::lean_dec_ref(v_toApplicative_3280_);
                v___x_3297_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once
                    ),
                    _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0,
                );
                v___f_3298_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once
                    ),
                    _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1,
                );
                if v_isShared_3295_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3294_, 7);
                    crate::leanh::lean_ctor_set(v___x_3294_, 1, v___x_3297_);
                    crate::leanh::lean_ctor_set(v___x_3294_, 0, v_msgData_3281_);
                    v___x_3300_ = v___x_3294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3308_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_msgData_3281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 1, v___x_3297_);
                    v___x_3300_ = v_reuseFailAlloc_3308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3301_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once
                    ),
                    _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4,
                );
                v___x_3302_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3302_, 0, v___x_3300_);
                crate::leanh::lean_ctor_set(v___x_3302_, 1, v___x_3301_);
                v___x_3303_ = l_Lean_MessageData_ofSyntax(v_after_3292_);
                v___x_3304_ = l_Lean_indentD(v___x_3303_);
                v_msgData_3305_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_3305_, 0, v___x_3302_);
                crate::leanh::lean_ctor_set(v_msgData_3305_, 1, v___x_3304_);
                v___x_3306_ =
                    l_List_foldl___redArg(v___f_3298_, v_msgData_3305_, v_macroStack_3282_);
                v___x_3307_ = crate::leanh::lean_apply_2(
                    v_toPure_3296_,
                    crate::leanh::lean_box(0),
                    v___x_3306_,
                );
                return v___x_3307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(
    mut v___x_3311_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3312_: *mut crate::leanh::LeanObject,
    mut v_msgData_3313_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3314_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3316_ = l_Lean_Elab_addMacroStack___redArg___lam__1(
        v___x_3311_,
        v_toApplicative_3312_,
        v_msgData_3313_,
        v_macroStack_3314_,
        v_____do__lift_3315_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_3315_);
    return v_res_3316_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___redArg(
    mut v_inst_3317_: *mut crate::leanh::LeanObject,
    mut v_inst_3318_: *mut crate::leanh::LeanObject,
    mut v_msgData_3319_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3321_ = l_Lean_KVMap_instValueBool;
    v_toApplicative_3322_ = crate::leanh::lean_ctor_get(v_inst_3317_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3322_);
    v_toBind_3323_ = crate::leanh::lean_ctor_get(v_inst_3317_, 1);
    crate::leanh::lean_inc(v_toBind_3323_);
    crate::leanh::lean_dec_ref(v_inst_3317_);
    v___f_3324_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_addMacroStack___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3324_, 0, v___x_3321_);
    crate::leanh::lean_closure_set(v___f_3324_, 1, v_toApplicative_3322_);
    crate::leanh::lean_closure_set(v___f_3324_, 2, v_msgData_3319_);
    crate::leanh::lean_closure_set(v___f_3324_, 3, v_macroStack_3320_);
    v___x_3325_ = crate::leanh::lean_apply_4(
        v_toBind_3323_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_3318_,
        v___f_3324_,
    );
    return v___x_3325_;
}
pub unsafe fn l_Lean_Elab_addMacroStack(
    mut v_m_3326_: *mut crate::leanh::LeanObject,
    mut v_inst_3327_: *mut crate::leanh::LeanObject,
    mut v_inst_3328_: *mut crate::leanh::LeanObject,
    mut v_msgData_3329_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3331_ = l_Lean_Elab_addMacroStack___redArg(
        v_inst_3327_,
        v_inst_3328_,
        v_msgData_3329_,
        v_macroStack_3330_,
    );
    return v___x_3331_;
}
pub unsafe fn _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3333_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0;
    v___x_3334_ = l_Lean_stringToMessageData(v___x_3333_);
    return v___x_3334_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(
    mut v_inst_3335_: *mut crate::leanh::LeanObject,
    mut v_inst_3336_: *mut crate::leanh::LeanObject,
    mut v_____r_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3338_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once),
        _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1,
    );
    v___x_3339_ = l_Lean_throwError___redArg(v_inst_3335_, v_inst_3336_, v___x_3338_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(
    mut v_k_3340_: *mut crate::leanh::LeanObject,
    mut v___f_3341_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3342_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3344_: u8 = 0;
    crate::leanh::lean_inc(v_k_3340_);
    v___x_3344_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_3343_, v_k_3340_);
    if v___x_3344_ == 0 {
        let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_3342_);
        crate::leanh::lean_dec(v_k_3340_);
        v___x_3345_ = crate::leanh::lean_box(0);
        v___x_3346_ = crate::leanh::lean_apply_1(v___f_3341_, v___x_3345_);
        return v___x_3346_;
    } else {
        let mut v_toPure_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_3341_);
        v_toPure_3347_ = crate::leanh::lean_ctor_get(v_toApplicative_3342_, 1);
        crate::leanh::lean_inc(v_toPure_3347_);
        crate::leanh::lean_dec_ref(v_toApplicative_3342_);
        v___x_3348_ =
            crate::leanh::lean_apply_2(v_toPure_3347_, crate::leanh::lean_box(0), v_k_3340_);
        return v___x_3348_;
    }
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(
    mut v_k_3349_: *mut crate::leanh::LeanObject,
    mut v___f_3350_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3351_: *mut crate::leanh::LeanObject,
    mut v_toBind_3352_: *mut crate::leanh::LeanObject,
    mut v_getEnv_3353_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_3355_ = l_Lean_mkPrivateName(v_____do__lift_3354_, v_k_3349_);
    v___f_3356_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3356_, 0, v_k_3355_);
    crate::leanh::lean_closure_set(v___f_3356_, 1, v___f_3350_);
    crate::leanh::lean_closure_set(v___f_3356_, 2, v_toApplicative_3351_);
    v___x_3357_ = crate::leanh::lean_apply_4(
        v_toBind_3352_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_3353_,
        v___f_3356_,
    );
    return v___x_3357_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(
    mut v_k_3358_: *mut crate::leanh::LeanObject,
    mut v___f_3359_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3360_: *mut crate::leanh::LeanObject,
    mut v_toBind_3361_: *mut crate::leanh::LeanObject,
    mut v_getEnv_3362_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3364_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(
        v_k_3358_,
        v___f_3359_,
        v_toApplicative_3360_,
        v_toBind_3361_,
        v_getEnv_3362_,
        v_____do__lift_3363_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_3363_);
    return v_res_3364_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(
    mut v___f_3365_: *mut crate::leanh::LeanObject,
    mut v_k_3366_: *mut crate::leanh::LeanObject,
    mut v_toBind_3367_: *mut crate::leanh::LeanObject,
    mut v_getEnv_3368_: *mut crate::leanh::LeanObject,
    mut v___f_3369_: *mut crate::leanh::LeanObject,
    mut v___x_3370_: u8,
    mut v_____do__lift_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: u8 = 0;
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isExporting_3379_ = crate::leanh::lean_ctor_get_uint8(
                    v_____do__lift_3371_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                if v_isExporting_3379_ == 0 {
                    state = 2;
                    continue;
                } else {
                    if v___x_3370_ == 0 {
                        crate::leanh::lean_dec(v___f_3369_);
                        crate::leanh::lean_dec(v_getEnv_3368_);
                        crate::leanh::lean_dec(v_toBind_3367_);
                        state = 1;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3373_ = crate::leanh::lean_box(0);
                v___x_3374_ = crate::leanh::lean_apply_1(v___f_3365_, v___x_3373_);
                return v___x_3374_;
            }
            2 => {
                v___x_3376_ = l_Lean_isPrivateName(v_k_3366_);
                if v___x_3376_ == 0 {
                    crate::leanh::lean_dec(v___f_3365_);
                    v___x_3377_ = crate::leanh::lean_apply_4(
                        v_toBind_3367_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_getEnv_3368_,
                        v___f_3369_,
                    );
                    return v___x_3377_;
                } else {
                    if v___x_3370_ == 0 {
                        crate::leanh::lean_dec(v___f_3369_);
                        crate::leanh::lean_dec(v_getEnv_3368_);
                        crate::leanh::lean_dec(v_toBind_3367_);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___f_3365_);
                        v___x_3378_ = crate::leanh::lean_apply_4(
                            v_toBind_3367_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_getEnv_3368_,
                            v___f_3369_,
                        );
                        return v___x_3378_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed(
    mut v___f_3380_: *mut crate::leanh::LeanObject,
    mut v_k_3381_: *mut crate::leanh::LeanObject,
    mut v_toBind_3382_: *mut crate::leanh::LeanObject,
    mut v_getEnv_3383_: *mut crate::leanh::LeanObject,
    mut v___f_3384_: *mut crate::leanh::LeanObject,
    mut v___x_3385_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_388__boxed_3387_: u8 = 0;
    let mut v_res_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_388__boxed_3387_ = (crate::leanh::lean_unbox(v___x_3385_) as u8);
    v_res_3388_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(
        v___f_3380_,
        v_k_3381_,
        v_toBind_3382_,
        v_getEnv_3383_,
        v___f_3384_,
        v___x_388__boxed_3387_,
        v_____do__lift_3386_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_3386_);
    crate::leanh::lean_dec(v_k_3381_);
    return v_res_3388_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(
    mut v_k_3389_: *mut crate::leanh::LeanObject,
    mut v___f_3390_: *mut crate::leanh::LeanObject,
    mut v_toBind_3391_: *mut crate::leanh::LeanObject,
    mut v_getEnv_3392_: *mut crate::leanh::LeanObject,
    mut v___f_3393_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_3394_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3396_: u8 = 0;
    crate::leanh::lean_inc(v_k_3389_);
    v___x_3396_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_3395_, v_k_3389_);
    if v___x_3396_ == 0 {
        let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_3394_);
        v___x_3397_ = crate::leanh::lean_box((v___x_3396_) as usize);
        crate::leanh::lean_inc(v_getEnv_3392_);
        crate::leanh::lean_inc(v_toBind_3391_);
        v___f_3398_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed as *mut core::ffi::c_void,
            7,
            6,
        );
        crate::leanh::lean_closure_set(v___f_3398_, 0, v___f_3390_);
        crate::leanh::lean_closure_set(v___f_3398_, 1, v_k_3389_);
        crate::leanh::lean_closure_set(v___f_3398_, 2, v_toBind_3391_);
        crate::leanh::lean_closure_set(v___f_3398_, 3, v_getEnv_3392_);
        crate::leanh::lean_closure_set(v___f_3398_, 4, v___f_3393_);
        crate::leanh::lean_closure_set(v___f_3398_, 5, v___x_3397_);
        v___x_3399_ = crate::leanh::lean_apply_4(
            v_toBind_3391_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_3392_,
            v___f_3398_,
        );
        return v___x_3399_;
    } else {
        let mut v_toPure_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_3393_);
        crate::leanh::lean_dec(v_getEnv_3392_);
        crate::leanh::lean_dec(v_toBind_3391_);
        crate::leanh::lean_dec(v___f_3390_);
        v_toPure_3400_ = crate::leanh::lean_ctor_get(v_toApplicative_3394_, 1);
        crate::leanh::lean_inc(v_toPure_3400_);
        crate::leanh::lean_dec_ref(v_toApplicative_3394_);
        v___x_3401_ =
            crate::leanh::lean_apply_2(v_toPure_3400_, crate::leanh::lean_box(0), v_k_3389_);
        return v___x_3401_;
    }
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg(
    mut v_inst_3402_: *mut crate::leanh::LeanObject,
    mut v_inst_3403_: *mut crate::leanh::LeanObject,
    mut v_inst_3404_: *mut crate::leanh::LeanObject,
    mut v_k_3405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3406_ = crate::leanh::lean_ctor_get(v_inst_3402_, 0);
    crate::leanh::lean_inc_ref_n(v_toApplicative_3406_, 2);
    v_toBind_3407_ = crate::leanh::lean_ctor_get(v_inst_3402_, 1);
    crate::leanh::lean_inc_n(v_toBind_3407_, 3);
    v_getEnv_3408_ = crate::leanh::lean_ctor_get(v_inst_3403_, 0);
    crate::leanh::lean_inc_n(v_getEnv_3408_, 3);
    crate::leanh::lean_dec_ref(v_inst_3403_);
    v___f_3409_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3409_, 0, v_inst_3402_);
    crate::leanh::lean_closure_set(v___f_3409_, 1, v_inst_3404_);
    crate::leanh::lean_inc_ref(v___f_3409_);
    crate::leanh::lean_inc(v_k_3405_);
    v___f_3410_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3410_, 0, v_k_3405_);
    crate::leanh::lean_closure_set(v___f_3410_, 1, v___f_3409_);
    crate::leanh::lean_closure_set(v___f_3410_, 2, v_toApplicative_3406_);
    crate::leanh::lean_closure_set(v___f_3410_, 3, v_toBind_3407_);
    crate::leanh::lean_closure_set(v___f_3410_, 4, v_getEnv_3408_);
    v___f_3411_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_3411_, 0, v_k_3405_);
    crate::leanh::lean_closure_set(v___f_3411_, 1, v___f_3409_);
    crate::leanh::lean_closure_set(v___f_3411_, 2, v_toBind_3407_);
    crate::leanh::lean_closure_set(v___f_3411_, 3, v_getEnv_3408_);
    crate::leanh::lean_closure_set(v___f_3411_, 4, v___f_3410_);
    crate::leanh::lean_closure_set(v___f_3411_, 5, v_toApplicative_3406_);
    v___x_3412_ = crate::leanh::lean_apply_4(
        v_toBind_3407_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_3408_,
        v___f_3411_,
    );
    return v___x_3412_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind(
    mut v_m_3413_: *mut crate::leanh::LeanObject,
    mut v_inst_3414_: *mut crate::leanh::LeanObject,
    mut v_inst_3415_: *mut crate::leanh::LeanObject,
    mut v_inst_3416_: *mut crate::leanh::LeanObject,
    mut v_k_3417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(
        v_inst_3414_,
        v_inst_3415_,
        v_inst_3416_,
        v_k_3417_,
    );
    return v___x_3418_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(
    mut v_inst_3419_: *mut crate::leanh::LeanObject,
    mut v_inst_3420_: *mut crate::leanh::LeanObject,
    mut v_inst_3421_: *mut crate::leanh::LeanObject,
    mut v_k_3422_: *mut crate::leanh::LeanObject,
    mut v_pre_3423_: *mut crate::leanh::LeanObject,
    mut v_x_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(
        v_inst_3419_,
        v_inst_3420_,
        v_inst_3421_,
        v_k_3422_,
        v_pre_3423_,
        v_x_3424_,
    );
    crate::leanh::lean_dec_ref(v_x_3424_);
    return v_res_3425_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(
    mut v_inst_3426_: *mut crate::leanh::LeanObject,
    mut v_inst_3427_: *mut crate::leanh::LeanObject,
    mut v_inst_3428_: *mut crate::leanh::LeanObject,
    mut v_k_3429_: *mut crate::leanh::LeanObject,
    mut v_x_3430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3430_) {
        1 => {
            let mut v_toMonadExceptOf_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_pre_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tryCatch_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toMonadExceptOf_3431_ = crate::leanh::lean_ctor_get(v_inst_3428_, 0);
            v_pre_3432_ = crate::leanh::lean_ctor_get(v_x_3430_, 0);
            v_tryCatch_3433_ = crate::leanh::lean_ctor_get(v_toMonadExceptOf_3431_, 1);
            crate::leanh::lean_inc(v_tryCatch_3433_);
            crate::leanh::lean_inc(v_pre_3432_);
            crate::leanh::lean_inc(v_k_3429_);
            crate::leanh::lean_inc_ref(v_inst_3428_);
            crate::leanh::lean_inc_ref(v_inst_3427_);
            crate::leanh::lean_inc_ref(v_inst_3426_);
            v___f_3434_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_3434_, 0, v_inst_3426_);
            crate::leanh::lean_closure_set(v___f_3434_, 1, v_inst_3427_);
            crate::leanh::lean_closure_set(v___f_3434_, 2, v_inst_3428_);
            crate::leanh::lean_closure_set(v___f_3434_, 3, v_k_3429_);
            crate::leanh::lean_closure_set(v___f_3434_, 4, v_pre_3432_);
            v___x_3435_ = l_Lean_Name_append(v_x_3430_, v_k_3429_);
            v___x_3436_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(
                v_inst_3426_,
                v_inst_3427_,
                v_inst_3428_,
                v___x_3435_,
            );
            v___x_3437_ = crate::leanh::lean_apply_3(
                v_tryCatch_3433_,
                crate::leanh::lean_box(0),
                v___x_3436_,
                v___f_3434_,
            );
            return v___x_3437_;
        }
        0 => {
            let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3438_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(
                v_inst_3426_,
                v_inst_3427_,
                v_inst_3428_,
                v_k_3429_,
            );
            return v___x_3438_;
        }
        _ => {
            let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3430_);
            crate::leanh::lean_dec(v_k_3429_);
            crate::leanh::lean_dec_ref(v_inst_3427_);
            v___x_3439_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once
                ),
                _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1,
            );
            v___x_3440_ = l_Lean_throwError___redArg(v_inst_3426_, v_inst_3428_, v___x_3439_);
            return v___x_3440_;
        }
    }
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(
    mut v_inst_3441_: *mut crate::leanh::LeanObject,
    mut v_inst_3442_: *mut crate::leanh::LeanObject,
    mut v_inst_3443_: *mut crate::leanh::LeanObject,
    mut v_k_3444_: *mut crate::leanh::LeanObject,
    mut v_pre_3445_: *mut crate::leanh::LeanObject,
    mut v_x_3446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3447_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(
        v_inst_3441_,
        v_inst_3442_,
        v_inst_3443_,
        v_k_3444_,
        v_pre_3445_,
    );
    return v___x_3447_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces(
    mut v_m_3448_: *mut crate::leanh::LeanObject,
    mut v_inst_3449_: *mut crate::leanh::LeanObject,
    mut v_inst_3450_: *mut crate::leanh::LeanObject,
    mut v_inst_3451_: *mut crate::leanh::LeanObject,
    mut v_k_3452_: *mut crate::leanh::LeanObject,
    mut v_x_3453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3454_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(
        v_inst_3449_,
        v_inst_3450_,
        v_inst_3451_,
        v_k_3452_,
        v_x_3453_,
    );
    return v___x_3454_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3455_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3455_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
    v___x_3457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3457_, 0, v___x_3456_);
    return v___x_3457_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3458_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
    v___x_3459_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3460_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3460_, 0, v___x_3459_);
    crate::leanh::lean_ctor_set(v___x_3460_, 1, v___x_3459_);
    crate::leanh::lean_ctor_set(v___x_3460_, 2, v___x_3459_);
    crate::leanh::lean_ctor_set(v___x_3460_, 3, v___x_3459_);
    crate::leanh::lean_ctor_set(v___x_3460_, 4, v___x_3458_);
    crate::leanh::lean_ctor_set(v___x_3460_, 5, v___x_3458_);
    crate::leanh::lean_ctor_set(v___x_3460_, 6, v___x_3458_);
    crate::leanh::lean_ctor_set(v___x_3460_, 7, v___x_3458_);
    crate::leanh::lean_ctor_set(v___x_3460_, 8, v___x_3458_);
    crate::leanh::lean_ctor_set(v___x_3460_, 9, v___x_3458_);
    return v___x_3460_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3461_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3462_ = lean_mk_empty_array_with_capacity(v___x_3461_);
    v___x_3463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3463_, 0, v___x_3462_);
    return v___x_3463_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3464_: usize = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3464_ = 5usize;
    v___x_3465_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3466_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3467_ = lean_mk_empty_array_with_capacity(v___x_3466_);
    v___x_3468_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3);
    v___x_3469_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3469_, 0, v___x_3468_);
    crate::leanh::lean_ctor_set(v___x_3469_, 1, v___x_3467_);
    crate::leanh::lean_ctor_set(v___x_3469_, 2, v___x_3465_);
    crate::leanh::lean_ctor_set(v___x_3469_, 3, v___x_3465_);
    crate::leanh::lean_ctor_set_usize(v___x_3469_, 4, v___x_3464_);
    return v___x_3469_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3470_ = crate::leanh::lean_box(1);
    v___x_3471_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4);
    v___x_3472_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
    v___x_3473_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3473_, 0, v___x_3472_);
    crate::leanh::lean_ctor_set(v___x_3473_, 1, v___x_3471_);
    crate::leanh::lean_ctor_set(v___x_3473_, 2, v___x_3470_);
    return v___x_3473_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(
    mut v_msgData_3474_: *mut crate::leanh::LeanObject,
    mut v___y_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3478_ = lean_st_ref_get(v___y_3476_);
    v_env_3479_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
    crate::leanh::lean_inc_ref(v_env_3479_);
    crate::leanh::lean_dec(v___x_3478_);
    v_options_3480_ = crate::leanh::lean_ctor_get(v___y_3475_, 2);
    v___x_3481_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
    v___x_3482_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
    crate::leanh::lean_inc_ref(v_options_3480_);
    v___x_3483_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3483_, 0, v_env_3479_);
    crate::leanh::lean_ctor_set(v___x_3483_, 1, v___x_3481_);
    crate::leanh::lean_ctor_set(v___x_3483_, 2, v___x_3482_);
    crate::leanh::lean_ctor_set(v___x_3483_, 3, v_options_3480_);
    v___x_3484_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3484_, 0, v___x_3483_);
    crate::leanh::lean_ctor_set(v___x_3484_, 1, v_msgData_3474_);
    v___x_3485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3485_, 0, v___x_3484_);
    return v___x_3485_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(
    mut v_msgData_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
    mut v___y_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3490_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_3486_, v___y_3487_, v___y_3488_);
    crate::leanh::lean_dec(v___y_3488_);
    crate::leanh::lean_dec_ref(v___y_3487_);
    return v_res_3490_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(
    mut v_msg_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_ref_3495_ = crate::leanh::lean_ctor_get(v___y_3492_, 5);
                v___x_3496_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_3491_, v___y_3492_, v___y_3493_);
                v_a_3497_ = crate::leanh::lean_ctor_get(v___x_3496_, 0);
                v_isSharedCheck_3505_ = (!crate::leanh::lean_is_exclusive(v___x_3496_)) as u8;
                if v_isSharedCheck_3505_ == 0 {
                    v___x_3499_ = v___x_3496_;
                    v_isShared_3500_ = v_isSharedCheck_3505_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3497_);
                    crate::leanh::lean_dec(v___x_3496_);
                    v___x_3499_ = crate::leanh::lean_box(0);
                    v_isShared_3500_ = v_isSharedCheck_3505_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3495_);
                v___x_3501_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3501_, 0, v_ref_3495_);
                crate::leanh::lean_ctor_set(v___x_3501_, 1, v_a_3497_);
                if v_isShared_3500_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3499_, 1);
                    crate::leanh::lean_ctor_set(v___x_3499_, 0, v___x_3501_);
                    v___x_3503_ = v___x_3499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
                    v___x_3503_ = v_reuseFailAlloc_3504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg___boxed(
    mut v_msg_3506_: *mut crate::leanh::LeanObject,
    mut v___y_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3510_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_3506_, v___y_3507_, v___y_3508_);
    crate::leanh::lean_dec(v___y_3508_);
    crate::leanh::lean_dec_ref(v___y_3507_);
    return v_res_3510_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(
    mut v_k_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3541_: u8 = 0;
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3520_ = lean_st_ref_get(v___y_3513_);
                v_env_3521_ = crate::leanh::lean_ctor_get(v___x_3520_, 0);
                crate::leanh::lean_inc_ref(v_env_3521_);
                crate::leanh::lean_dec(v___x_3520_);
                crate::leanh::lean_inc(v_k_3511_);
                v___x_3522_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3521_, v_k_3511_);
                if v___x_3522_ == 0 {
                    v___x_3523_ = lean_st_ref_get(v___y_3513_);
                    v_env_3540_ = crate::leanh::lean_ctor_get(v___x_3523_, 0);
                    crate::leanh::lean_inc_ref(v_env_3540_);
                    crate::leanh::lean_dec(v___x_3523_);
                    v_isExporting_3541_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_3540_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    crate::leanh::lean_dec_ref(v_env_3540_);
                    if v_isExporting_3541_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        if v___x_3522_ == 0 {
                            crate::leanh::lean_dec(v_k_3511_);
                            v___y_3516_ = v___y_3512_;
                            v___y_3517_ = v___y_3513_;
                            state = 1;
                            continue;
                        } else {
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3542_, 0, v_k_3511_);
                    return v___x_3542_;
                }
            }
            1 => {
                v___x_3518_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1,
                );
                v___x_3519_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_3518_, v___y_3516_, v___y_3517_);
                return v___x_3519_;
            }
            2 => {
                v___x_3525_ = l_Lean_isPrivateName(v_k_3511_);
                if v___x_3525_ == 0 {
                    v___x_3526_ = lean_st_ref_get(v___y_3513_);
                    v_env_3527_ = crate::leanh::lean_ctor_get(v___x_3526_, 0);
                    crate::leanh::lean_inc_ref(v_env_3527_);
                    crate::leanh::lean_dec(v___x_3526_);
                    v___x_3528_ = lean_st_ref_get(v___y_3513_);
                    v_env_3529_ = crate::leanh::lean_ctor_get(v___x_3528_, 0);
                    crate::leanh::lean_inc_ref(v_env_3529_);
                    crate::leanh::lean_dec(v___x_3528_);
                    v_k_3530_ = l_Lean_mkPrivateName(v_env_3527_, v_k_3511_);
                    crate::leanh::lean_dec_ref(v_env_3527_);
                    crate::leanh::lean_inc(v_k_3530_);
                    v___x_3531_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3529_, v_k_3530_);
                    if v___x_3531_ == 0 {
                        crate::leanh::lean_dec(v_k_3530_);
                        v___y_3516_ = v___y_3512_;
                        v___y_3517_ = v___y_3513_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3532_, 0, v_k_3530_);
                        return v___x_3532_;
                    }
                } else {
                    if v___x_3522_ == 0 {
                        crate::leanh::lean_dec(v_k_3511_);
                        v___y_3516_ = v___y_3512_;
                        v___y_3517_ = v___y_3513_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3533_ = lean_st_ref_get(v___y_3513_);
                        v_env_3534_ = crate::leanh::lean_ctor_get(v___x_3533_, 0);
                        crate::leanh::lean_inc_ref(v_env_3534_);
                        crate::leanh::lean_dec(v___x_3533_);
                        v___x_3535_ = lean_st_ref_get(v___y_3513_);
                        v_env_3536_ = crate::leanh::lean_ctor_get(v___x_3535_, 0);
                        crate::leanh::lean_inc_ref(v_env_3536_);
                        crate::leanh::lean_dec(v___x_3535_);
                        v_k_3537_ = l_Lean_mkPrivateName(v_env_3534_, v_k_3511_);
                        crate::leanh::lean_dec_ref(v_env_3534_);
                        crate::leanh::lean_inc(v_k_3537_);
                        v___x_3538_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3536_, v_k_3537_);
                        if v___x_3538_ == 0 {
                            crate::leanh::lean_dec(v_k_3537_);
                            v___y_3516_ = v___y_3512_;
                            v___y_3517_ = v___y_3513_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3539_, 0, v_k_3537_);
                            return v___x_3539_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0___boxed(
    mut v_k_3543_: *mut crate::leanh::LeanObject,
    mut v___y_3544_: *mut crate::leanh::LeanObject,
    mut v___y_3545_: *mut crate::leanh::LeanObject,
    mut v___y_3546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_3543_, v___y_3544_, v___y_3545_);
    crate::leanh::lean_dec(v___y_3545_);
    crate::leanh::lean_dec_ref(v___y_3544_);
    return v_res_3547_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(
    mut v_k_3548_: *mut crate::leanh::LeanObject,
    mut v_x_3549_: *mut crate::leanh::LeanObject,
    mut v___y_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pre_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3558_: u8 = 0;
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: u8 = 0;
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3549_) {
                1 => {
                    v_pre_3553_ = crate::leanh::lean_ctor_get(v_x_3549_, 0);
                    crate::leanh::lean_inc(v_pre_3553_);
                    crate::leanh::lean_inc(v_k_3548_);
                    v___x_3554_ = l_Lean_Name_append(v_x_3549_, v_k_3548_);
                    v___x_3555_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_3554_, v___y_3550_, v___y_3551_);
                    if crate::leanh::lean_obj_tag(v___x_3555_) == 0 {
                        crate::leanh::lean_dec(v_pre_3553_);
                        crate::leanh::lean_dec(v_k_3548_);
                        return v___x_3555_;
                    } else {
                        v_a_3556_ = crate::leanh::lean_ctor_get(v___x_3555_, 0);
                        crate::leanh::lean_inc(v_a_3556_);
                        v___x_3560_ = l_Lean_Exception_isInterrupt(v_a_3556_);
                        if v___x_3560_ == 0 {
                            v___x_3561_ = l_Lean_Exception_isRuntime(v_a_3556_);
                            v___y_3558_ = v___x_3561_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3556_);
                            v___y_3558_ = v___x_3560_;
                            state = 1;
                            continue;
                        }
                    }
                }
                0 => {
                    v___x_3562_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_3548_, v___y_3550_, v___y_3551_);
                    return v___x_3562_;
                }
                _ => {
                    crate::leanh::lean_dec(v_x_3549_);
                    crate::leanh::lean_dec(v_k_3548_);
                    v___x_3563_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1,
                    );
                    v___x_3564_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_3563_, v___y_3550_, v___y_3551_);
                    return v___x_3564_;
                }
            },
            1 => {
                if v___y_3558_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3555_, 1);
                    v_x_3549_ = v_pre_3553_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_pre_3553_);
                    crate::leanh::lean_dec(v_k_3548_);
                    return v___x_3555_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(
    mut v_k_3565_: *mut crate::leanh::LeanObject,
    mut v_x_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
    mut v___y_3568_: *mut crate::leanh::LeanObject,
    mut v___y_3569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3570_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_3565_, v_x_3566_, v___y_3567_, v___y_3568_);
    crate::leanh::lean_dec(v___y_3568_);
    crate::leanh::lean_dec_ref(v___y_3567_);
    return v_res_3570_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(
    mut v_k_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currNamespace_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_currNamespace_3575_ = crate::leanh::lean_ctor_get(v_a_3572_, 6);
    crate::leanh::lean_inc(v_currNamespace_3575_);
    v___x_3576_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_3571_, v_currNamespace_3575_, v_a_3572_, v_a_3573_);
    return v___x_3576_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(
    mut v_k_3577_: *mut crate::leanh::LeanObject,
    mut v_a_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3581_ =
        l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_3577_, v_a_3578_, v_a_3579_);
    crate::leanh::lean_dec(v_a_3579_);
    crate::leanh::lean_dec_ref(v_a_3578_);
    return v_res_3581_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(
    mut v_00_u03b1_3582_: *mut crate::leanh::LeanObject,
    mut v_msg_3583_: *mut crate::leanh::LeanObject,
    mut v___y_3584_: *mut crate::leanh::LeanObject,
    mut v___y_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3587_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_3583_, v___y_3584_, v___y_3585_);
    return v___x_3587_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(
    mut v_00_u03b1_3588_: *mut crate::leanh::LeanObject,
    mut v_msg_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
    mut v___y_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3593_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(v_00_u03b1_3588_, v_msg_3589_, v___y_3590_, v___y_3591_);
    crate::leanh::lean_dec(v___y_3591_);
    crate::leanh::lean_dec_ref(v___y_3590_);
    return v_res_3593_;
}
pub unsafe fn _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3595_ = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0;
    v___x_3596_ = l_Lean_stringToMessageData(v___x_3595_);
    return v___x_3596_;
}
pub unsafe fn _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
    v___x_3599_ = l_Lean_stringToMessageData(v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Lean_Elab_syntaxNodeKindOfAttrParam(
    mut v_defaultParserNamespace_3600_: *mut crate::leanh::LeanObject,
    mut v_stx_3601_: *mut crate::leanh::LeanObject,
    mut v_a_3602_: *mut crate::leanh::LeanObject,
    mut v_a_3603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3609_: u8 = 0;
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3619_: u8 = 0;
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___x_3624_: u8 = 0;
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3605_ = l_Lean_Attribute_Builtin_getId(v_stx_3601_, v_a_3602_, v_a_3603_);
                if crate::leanh::lean_obj_tag(v___x_3605_) == 0 {
                    v_a_3606_ = crate::leanh::lean_ctor_get(v___x_3605_, 0);
                    crate::leanh::lean_inc_n(v_a_3606_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3605_, 1);
                    v___x_3616_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(
                        v_a_3606_, v_a_3602_, v_a_3603_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3616_) == 0 {
                        crate::leanh::lean_dec(v_a_3606_);
                        crate::leanh::lean_dec(v_defaultParserNamespace_3600_);
                        return v___x_3616_;
                    } else {
                        v_a_3617_ = crate::leanh::lean_ctor_get(v___x_3616_, 0);
                        crate::leanh::lean_inc(v_a_3617_);
                        v___x_3625_ = l_Lean_Exception_isInterrupt(v_a_3617_);
                        if v___x_3625_ == 0 {
                            v___x_3626_ = l_Lean_Exception_isRuntime(v_a_3617_);
                            v___y_3619_ = v___x_3626_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3617_);
                            v___y_3619_ = v___x_3625_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_defaultParserNamespace_3600_);
                    return v___x_3605_;
                }
            }
            1 => {
                if v___y_3609_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3608_);
                    v___x_3610_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once
                        ),
                        _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1,
                    );
                    v___x_3611_ = l_Lean_MessageData_ofName(v_a_3606_);
                    v___x_3612_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3612_, 0, v___x_3610_);
                    crate::leanh::lean_ctor_set(v___x_3612_, 1, v___x_3611_);
                    v___x_3613_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once
                        ),
                        _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3,
                    );
                    v___x_3614_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3614_, 0, v___x_3612_);
                    crate::leanh::lean_ctor_set(v___x_3614_, 1, v___x_3613_);
                    v___x_3615_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_3614_, v_a_3602_, v_a_3603_);
                    return v___x_3615_;
                } else {
                    crate::leanh::lean_dec(v_a_3606_);
                    return v___y_3608_;
                }
            }
            2 => {
                if v___y_3619_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3616_, 1);
                    crate::leanh::lean_inc(v_a_3606_);
                    v___x_3620_ = l_Lean_Name_append(v_defaultParserNamespace_3600_, v_a_3606_);
                    v___x_3621_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_3620_, v_a_3602_, v_a_3603_);
                    if crate::leanh::lean_obj_tag(v___x_3621_) == 0 {
                        crate::leanh::lean_dec(v_a_3606_);
                        return v___x_3621_;
                    } else {
                        v_a_3622_ = crate::leanh::lean_ctor_get(v___x_3621_, 0);
                        crate::leanh::lean_inc(v_a_3622_);
                        v___x_3623_ = l_Lean_Exception_isInterrupt(v_a_3622_);
                        if v___x_3623_ == 0 {
                            v___x_3624_ = l_Lean_Exception_isRuntime(v_a_3622_);
                            v___y_3608_ = v___x_3621_;
                            v___y_3609_ = v___x_3624_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3622_);
                            v___y_3608_ = v___x_3621_;
                            v___y_3609_ = v___x_3623_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3606_);
                    crate::leanh::lean_dec(v_defaultParserNamespace_3600_);
                    return v___x_3616_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(
    mut v_defaultParserNamespace_3627_: *mut crate::leanh::LeanObject,
    mut v_stx_3628_: *mut crate::leanh::LeanObject,
    mut v_a_3629_: *mut crate::leanh::LeanObject,
    mut v_a_3630_: *mut crate::leanh::LeanObject,
    mut v_a_3631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3632_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(
        v_defaultParserNamespace_3627_,
        v_stx_3628_,
        v_a_3629_,
        v_a_3630_,
    );
    crate::leanh::lean_dec(v_a_3630_);
    crate::leanh::lean_dec_ref(v_a_3629_);
    return v_res_3632_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(
    mut v_env_3637_: *mut crate::leanh::LeanObject,
    mut v_opts_3638_: *mut crate::leanh::LeanObject,
    mut v_constName_3639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3640_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1;
    v___x_3641_ = l_Lean_Environment_evalConstCheck___redArg(
        v_env_3637_,
        v_opts_3638_,
        v___x_3640_,
        v_constName_3639_,
    );
    return v___x_3641_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___boxed(
    mut v_env_3642_: *mut crate::leanh::LeanObject,
    mut v_opts_3643_: *mut crate::leanh::LeanObject,
    mut v_constName_3644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3645_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(
        v_env_3642_,
        v_opts_3643_,
        v_constName_3644_,
    );
    crate::leanh::lean_dec_ref(v_opts_3643_);
    return v_res_3645_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3670_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__8;
    v___x_3671_ = l_Lean_mkAtom(v___x_3670_);
    return v___x_3671_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10,
    );
    v___x_3673_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3674_ = lean_array_push(v___x_3673_, v___x_3672_);
    return v___x_3674_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3683_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__15;
    v___x_3684_ = l_Lean_mkAtom(v___x_3683_);
    return v___x_3684_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3685_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16,
    );
    v___x_3686_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3687_ = lean_array_push(v___x_3686_, v___x_3685_);
    return v___x_3687_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3688_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17,
    );
    v___x_3689_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__14;
    v___x_3690_ = crate::leanh::lean_box(2);
    v___x_3691_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3691_, 0, v___x_3690_);
    crate::leanh::lean_ctor_set(v___x_3691_, 1, v___x_3689_);
    crate::leanh::lean_ctor_set(v___x_3691_, 2, v___x_3688_);
    return v___x_3691_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3692_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18,
    );
    v___x_3693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11,
    );
    v___x_3694_ = lean_array_push(v___x_3693_, v___x_3692_);
    return v___x_3694_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3695_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19,
    );
    v___x_3696_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__9;
    v___x_3697_ = crate::leanh::lean_box(2);
    v___x_3698_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3698_, 0, v___x_3697_);
    crate::leanh::lean_ctor_set(v___x_3698_, 1, v___x_3696_);
    crate::leanh::lean_ctor_set(v___x_3698_, 2, v___x_3695_);
    return v___x_3698_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3699_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20,
    );
    v___x_3700_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3701_ = lean_array_push(v___x_3700_, v___x_3699_);
    return v___x_3701_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3702_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21,
    );
    v___x_3703_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__7;
    v___x_3704_ = crate::leanh::lean_box(2);
    v___x_3705_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3705_, 0, v___x_3704_);
    crate::leanh::lean_ctor_set(v___x_3705_, 1, v___x_3703_);
    crate::leanh::lean_ctor_set(v___x_3705_, 2, v___x_3702_);
    return v___x_3705_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3706_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22,
    );
    v___x_3707_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3708_ = lean_array_push(v___x_3707_, v___x_3706_);
    return v___x_3708_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3709_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23,
    );
    v___x_3710_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__5;
    v___x_3711_ = crate::leanh::lean_box(2);
    v___x_3712_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3712_, 0, v___x_3711_);
    crate::leanh::lean_ctor_set(v___x_3712_, 1, v___x_3710_);
    crate::leanh::lean_ctor_set(v___x_3712_, 2, v___x_3709_);
    return v___x_3712_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3713_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24,
    );
    v___x_3714_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3715_ = lean_array_push(v___x_3714_, v___x_3713_);
    return v___x_3715_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3716_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25,
    );
    v___x_3717_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__2;
    v___x_3718_ = crate::leanh::lean_box(2);
    v___x_3719_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3719_, 0, v___x_3718_);
    crate::leanh::lean_ctor_set(v___x_3719_, 1, v___x_3717_);
    crate::leanh::lean_ctor_set(v___x_3719_, 2, v___x_3716_);
    return v___x_3719_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26,
    );
    return v___x_3720_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg___lam__0(
    mut v_builtin_3721_: u8,
    mut v_declName_3722_: *mut crate::leanh::LeanObject,
    mut v_kind_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_builtin_3721_ == 0 {
        let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_declName_3722_);
        v___x_3727_ = crate::leanh::lean_box(0);
        v___x_3728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3728_, 0, v___x_3727_);
        return v___x_3728_;
    } else {
        let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3729_ =
            l_Lean_declareBuiltinDocStringAndRanges(v_declName_3722_, v___y_3724_, v___y_3725_);
        return v___x_3729_;
    }
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(
    mut v_builtin_3730_: *mut crate::leanh::LeanObject,
    mut v_declName_3731_: *mut crate::leanh::LeanObject,
    mut v_kind_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
    mut v___y_3734_: *mut crate::leanh::LeanObject,
    mut v___y_3735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_builtin_boxed_3736_: u8 = 0;
    let mut v_res_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3736_ = (crate::leanh::lean_unbox(v_builtin_3730_) as u8);
    v_res_3737_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(
        v_builtin_boxed_3736_,
        v_declName_3731_,
        v_kind_3732_,
        v___y_3733_,
        v___y_3734_,
    );
    crate::leanh::lean_dec(v___y_3734_);
    crate::leanh::lean_dec_ref(v___y_3733_);
    crate::leanh::lean_dec(v_kind_3732_);
    return v_res_3737_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(
    mut v_t_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_3743_: u8 = 0;
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3758_: u8 = 0;
    let mut v_enabled_3759_: u8 = 0;
    let mut v_assignment_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_isSharedCheck_3777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3741_ = lean_st_ref_get(v___y_3739_);
                v_infoState_3742_ = crate::leanh::lean_ctor_get(v___x_3741_, 7);
                crate::leanh::lean_inc_ref(v_infoState_3742_);
                crate::leanh::lean_dec(v___x_3741_);
                v_enabled_3743_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_3742_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_3742_);
                if v_enabled_3743_ == 0 {
                    crate::leanh::lean_dec_ref(v_t_3738_);
                    v___x_3744_ = crate::leanh::lean_box(0);
                    v___x_3745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3745_, 0, v___x_3744_);
                    return v___x_3745_;
                } else {
                    v___x_3746_ = lean_st_ref_take(v___y_3739_);
                    v_infoState_3747_ = crate::leanh::lean_ctor_get(v___x_3746_, 7);
                    v_env_3748_ = crate::leanh::lean_ctor_get(v___x_3746_, 0);
                    v_nextMacroScope_3749_ = crate::leanh::lean_ctor_get(v___x_3746_, 1);
                    v_ngen_3750_ = crate::leanh::lean_ctor_get(v___x_3746_, 2);
                    v_auxDeclNGen_3751_ = crate::leanh::lean_ctor_get(v___x_3746_, 3);
                    v_traceState_3752_ = crate::leanh::lean_ctor_get(v___x_3746_, 4);
                    v_cache_3753_ = crate::leanh::lean_ctor_get(v___x_3746_, 5);
                    v_messages_3754_ = crate::leanh::lean_ctor_get(v___x_3746_, 6);
                    v_snapshotTasks_3755_ = crate::leanh::lean_ctor_get(v___x_3746_, 8);
                    v_isSharedCheck_3777_ = (!crate::leanh::lean_is_exclusive(v___x_3746_)) as u8;
                    if v_isSharedCheck_3777_ == 0 {
                        v___x_3757_ = v___x_3746_;
                        v_isShared_3758_ = v_isSharedCheck_3777_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_3755_);
                        crate::leanh::lean_inc(v_infoState_3747_);
                        crate::leanh::lean_inc(v_messages_3754_);
                        crate::leanh::lean_inc(v_cache_3753_);
                        crate::leanh::lean_inc(v_traceState_3752_);
                        crate::leanh::lean_inc(v_auxDeclNGen_3751_);
                        crate::leanh::lean_inc(v_ngen_3750_);
                        crate::leanh::lean_inc(v_nextMacroScope_3749_);
                        crate::leanh::lean_inc(v_env_3748_);
                        crate::leanh::lean_dec(v___x_3746_);
                        v___x_3757_ = crate::leanh::lean_box(0);
                        v_isShared_3758_ = v_isSharedCheck_3777_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_3759_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_3747_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_3760_ = crate::leanh::lean_ctor_get(v_infoState_3747_, 0);
                v_lazyAssignment_3761_ = crate::leanh::lean_ctor_get(v_infoState_3747_, 1);
                v_trees_3762_ = crate::leanh::lean_ctor_get(v_infoState_3747_, 2);
                v_isSharedCheck_3776_ = (!crate::leanh::lean_is_exclusive(v_infoState_3747_)) as u8;
                if v_isSharedCheck_3776_ == 0 {
                    v___x_3764_ = v_infoState_3747_;
                    v_isShared_3765_ = v_isSharedCheck_3776_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trees_3762_);
                    crate::leanh::lean_inc(v_lazyAssignment_3761_);
                    crate::leanh::lean_inc(v_assignment_3760_);
                    crate::leanh::lean_dec(v_infoState_3747_);
                    v___x_3764_ = crate::leanh::lean_box(0);
                    v_isShared_3765_ = v_isSharedCheck_3776_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3766_ = l_Lean_PersistentArray_push___redArg(v_trees_3762_, v_t_3738_);
                if v_isShared_3765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3764_, 2, v___x_3766_);
                    v___x_3768_ = v___x_3764_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_assignment_3760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_lazyAssignment_3761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 2, v___x_3766_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3775_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_3759_,
                    );
                    v___x_3768_ = v_reuseFailAlloc_3775_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3757_, 7, v___x_3768_);
                    v___x_3770_ = v___x_3757_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_env_3748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_nextMacroScope_3749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_ngen_3750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 3, v_auxDeclNGen_3751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 4, v_traceState_3752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 5, v_cache_3753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 6, v_messages_3754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 7, v___x_3768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 8, v_snapshotTasks_3755_);
                    v___x_3770_ = v_reuseFailAlloc_3774_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3771_ = lean_st_ref_set(v___y_3739_, v___x_3770_);
                v___x_3772_ = crate::leanh::lean_box(0);
                v___x_3773_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3773_, 0, v___x_3772_);
                return v___x_3773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(
    mut v_t_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3781_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_3778_, v___y_3779_);
    crate::leanh::lean_dec(v___y_3779_);
    return v_res_3781_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3782_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3783_ = lean_mk_empty_array_with_capacity(v___x_3782_);
    v___x_3784_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3784_, 0, v___x_3783_);
    return v___x_3784_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3785_: usize = 0;
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = 5usize;
    v___x_3786_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3787_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3788_ = lean_mk_empty_array_with_capacity(v___x_3787_);
    v___x_3789_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0);
    v___x_3790_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3790_, 0, v___x_3789_);
    crate::leanh::lean_ctor_set(v___x_3790_, 1, v___x_3788_);
    crate::leanh::lean_ctor_set(v___x_3790_, 2, v___x_3786_);
    crate::leanh::lean_ctor_set(v___x_3790_, 3, v___x_3786_);
    crate::leanh::lean_ctor_set_usize(v___x_3790_, 4, v___x_3785_);
    return v___x_3790_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(
    mut v_t_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_3797_: u8 = 0;
    v___x_3795_ = lean_st_ref_get(v___y_3793_);
    v_infoState_3796_ = crate::leanh::lean_ctor_get(v___x_3795_, 7);
    crate::leanh::lean_inc_ref(v_infoState_3796_);
    crate::leanh::lean_dec(v___x_3795_);
    v_enabled_3797_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_3796_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_3796_);
    if v_enabled_3797_ == 0 {
        let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_t_3791_);
        v___x_3798_ = crate::leanh::lean_box(0);
        v___x_3799_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3799_, 0, v___x_3798_);
        return v___x_3799_;
    } else {
        let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3800_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1);
        v___x_3801_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3801_, 0, v_t_3791_);
        crate::leanh::lean_ctor_set(v___x_3801_, 1, v___x_3800_);
        v___x_3802_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v___x_3801_, v___y_3793_);
        return v___x_3802_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(
    mut v_t_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
    mut v___y_3805_: *mut crate::leanh::LeanObject,
    mut v___y_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3807_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_3803_, v___y_3804_, v___y_3805_);
    crate::leanh::lean_dec(v___y_3805_);
    crate::leanh::lean_dec_ref(v___y_3804_);
    return v_res_3807_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3809_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0;
    v___x_3810_ = l_Lean_stringToMessageData(v___x_3809_);
    return v___x_3810_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2;
    v___x_3813_ = l_Lean_stringToMessageData(v___x_3812_);
    return v___x_3813_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4;
    v___x_3816_ = l_Lean_stringToMessageData(v___x_3815_);
    return v___x_3816_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3818_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6;
    v___x_3819_ = l_Lean_stringToMessageData(v___x_3818_);
    return v___x_3819_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8;
    v___x_3822_ = l_Lean_stringToMessageData(v___x_3821_);
    return v___x_3822_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3824_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10;
    v___x_3825_ = l_Lean_stringToMessageData(v___x_3824_);
    return v___x_3825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12;
    v___x_3828_ = l_Lean_stringToMessageData(v___x_3827_);
    return v___x_3828_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(
    mut v_msg_3829_: *mut crate::leanh::LeanObject,
    mut v_declHint_3830_: *mut crate::leanh::LeanObject,
    mut v___y_3831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: u8 = 0;
    let mut v_isExporting_3836_: u8 = 0;
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3858_: u8 = 0;
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3833_ = lean_st_ref_get(v___y_3831_);
                v_env_3834_ = crate::leanh::lean_ctor_get(v___x_3833_, 0);
                crate::leanh::lean_inc_ref(v_env_3834_);
                crate::leanh::lean_dec(v___x_3833_);
                v___x_3835_ = l_Lean_Name_isAnonymous(v_declHint_3830_);
                if v___x_3835_ == 0 {
                    v_isExporting_3836_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_3834_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3836_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_3834_);
                        crate::leanh::lean_dec(v_declHint_3830_);
                        v___x_3837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3837_, 0, v_msg_3829_);
                        return v___x_3837_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_3834_);
                        v___x_3838_ = l_Lean_Environment_setExporting(v_env_3834_, v___x_3835_);
                        crate::leanh::lean_inc(v_declHint_3830_);
                        crate::leanh::lean_inc_ref(v___x_3838_);
                        v___x_3839_ = l_Lean_Environment_contains(
                            v___x_3838_,
                            v_declHint_3830_,
                            v_isExporting_3836_,
                        );
                        if v___x_3839_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3838_);
                            crate::leanh::lean_dec_ref(v_env_3834_);
                            crate::leanh::lean_dec(v_declHint_3830_);
                            v___x_3840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3840_, 0, v_msg_3829_);
                            return v___x_3840_;
                        } else {
                            v___x_3841_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
                            v___x_3842_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
                            v___x_3843_ = l_Lean_Options_empty;
                            v___x_3844_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3844_, 0, v___x_3838_);
                            crate::leanh::lean_ctor_set(v___x_3844_, 1, v___x_3841_);
                            crate::leanh::lean_ctor_set(v___x_3844_, 2, v___x_3842_);
                            crate::leanh::lean_ctor_set(v___x_3844_, 3, v___x_3843_);
                            crate::leanh::lean_inc(v_declHint_3830_);
                            v___x_3845_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3830_, v___x_3835_);
                            v_c_3846_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_3846_, 0, v___x_3844_);
                            crate::leanh::lean_ctor_set(v_c_3846_, 1, v___x_3845_);
                            v___x_3847_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3834_,
                                v_declHint_3830_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3847_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_3834_);
                                crate::leanh::lean_dec(v_declHint_3830_);
                                v___x_3848_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
                                v___x_3849_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3849_, 0, v___x_3848_);
                                crate::leanh::lean_ctor_set(v___x_3849_, 1, v_c_3846_);
                                v___x_3850_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
                                v___x_3851_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3851_, 0, v___x_3849_);
                                crate::leanh::lean_ctor_set(v___x_3851_, 1, v___x_3850_);
                                v___x_3852_ = l_Lean_MessageData_note(v___x_3851_);
                                v___x_3853_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3853_, 0, v_msg_3829_);
                                crate::leanh::lean_ctor_set(v___x_3853_, 1, v___x_3852_);
                                v___x_3854_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3854_, 0, v___x_3853_);
                                return v___x_3854_;
                            } else {
                                v_val_3855_ = crate::leanh::lean_ctor_get(v___x_3847_, 0);
                                v_isSharedCheck_3890_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3847_)) as u8;
                                if v_isSharedCheck_3890_ == 0 {
                                    v___x_3857_ = v___x_3847_;
                                    v_isShared_3858_ = v_isSharedCheck_3890_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3855_);
                                    crate::leanh::lean_dec(v___x_3847_);
                                    v___x_3857_ = crate::leanh::lean_box(0);
                                    v_isShared_3858_ = v_isSharedCheck_3890_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3834_);
                    crate::leanh::lean_dec(v_declHint_3830_);
                    v___x_3891_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3891_, 0, v_msg_3829_);
                    return v___x_3891_;
                }
            }
            1 => {
                v___x_3859_ = crate::leanh::lean_box(0);
                v___x_3860_ = l_Lean_Environment_header(v_env_3834_);
                crate::leanh::lean_dec_ref(v_env_3834_);
                v___x_3861_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3860_);
                v_mod_3862_ = lean_array_get(v___x_3859_, v___x_3861_, v_val_3855_);
                crate::leanh::lean_dec(v_val_3855_);
                crate::leanh::lean_dec_ref(v___x_3861_);
                v___x_3863_ = l_Lean_isPrivateName(v_declHint_3830_);
                crate::leanh::lean_dec(v_declHint_3830_);
                if v___x_3863_ == 0 {
                    v___x_3864_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
                    v___x_3865_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3865_, 0, v___x_3864_);
                    crate::leanh::lean_ctor_set(v___x_3865_, 1, v_c_3846_);
                    v___x_3866_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
                    v___x_3867_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3867_, 0, v___x_3865_);
                    crate::leanh::lean_ctor_set(v___x_3867_, 1, v___x_3866_);
                    v___x_3868_ = l_Lean_MessageData_ofName(v_mod_3862_);
                    v___x_3869_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3869_, 0, v___x_3867_);
                    crate::leanh::lean_ctor_set(v___x_3869_, 1, v___x_3868_);
                    v___x_3870_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
                    v___x_3871_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3871_, 0, v___x_3869_);
                    crate::leanh::lean_ctor_set(v___x_3871_, 1, v___x_3870_);
                    v___x_3872_ = l_Lean_MessageData_note(v___x_3871_);
                    v___x_3873_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3873_, 0, v_msg_3829_);
                    crate::leanh::lean_ctor_set(v___x_3873_, 1, v___x_3872_);
                    if v_isShared_3858_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3857_, 0);
                        crate::leanh::lean_ctor_set(v___x_3857_, 0, v___x_3873_);
                        v___x_3875_ = v___x_3857_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3876_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
                        v___x_3875_ = v_reuseFailAlloc_3876_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3877_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
                    v___x_3878_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3878_, 0, v___x_3877_);
                    crate::leanh::lean_ctor_set(v___x_3878_, 1, v_c_3846_);
                    v___x_3879_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
                    v___x_3880_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3880_, 0, v___x_3878_);
                    crate::leanh::lean_ctor_set(v___x_3880_, 1, v___x_3879_);
                    v___x_3881_ = l_Lean_MessageData_ofName(v_mod_3862_);
                    v___x_3882_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3880_);
                    crate::leanh::lean_ctor_set(v___x_3882_, 1, v___x_3881_);
                    v___x_3883_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
                    v___x_3884_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3884_, 0, v___x_3882_);
                    crate::leanh::lean_ctor_set(v___x_3884_, 1, v___x_3883_);
                    v___x_3885_ = l_Lean_MessageData_note(v___x_3884_);
                    v___x_3886_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3886_, 0, v_msg_3829_);
                    crate::leanh::lean_ctor_set(v___x_3886_, 1, v___x_3885_);
                    if v_isShared_3858_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3857_, 0);
                        crate::leanh::lean_ctor_set(v___x_3857_, 0, v___x_3886_);
                        v___x_3888_ = v___x_3857_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3889_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
                        v___x_3888_ = v_reuseFailAlloc_3889_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3875_;
            }
            3 => {
                return v___x_3888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___boxed(
    mut v_msg_3892_: *mut crate::leanh::LeanObject,
    mut v_declHint_3893_: *mut crate::leanh::LeanObject,
    mut v___y_3894_: *mut crate::leanh::LeanObject,
    mut v___y_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3896_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_3892_, v_declHint_3893_, v___y_3894_);
    crate::leanh::lean_dec(v___y_3894_);
    return v_res_3896_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(
    mut v_msg_3897_: *mut crate::leanh::LeanObject,
    mut v_declHint_3898_: *mut crate::leanh::LeanObject,
    mut v___y_3899_: *mut crate::leanh::LeanObject,
    mut v___y_3900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_3897_, v_declHint_3898_, v___y_3900_);
                v_a_3903_ = crate::leanh::lean_ctor_get(v___x_3902_, 0);
                v_isSharedCheck_3912_ = (!crate::leanh::lean_is_exclusive(v___x_3902_)) as u8;
                if v_isSharedCheck_3912_ == 0 {
                    v___x_3905_ = v___x_3902_;
                    v_isShared_3906_ = v_isSharedCheck_3912_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3903_);
                    crate::leanh::lean_dec(v___x_3902_);
                    v___x_3905_ = crate::leanh::lean_box(0);
                    v_isShared_3906_ = v_isSharedCheck_3912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3907_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3908_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3908_, 0, v___x_3907_);
                crate::leanh::lean_ctor_set(v___x_3908_, 1, v_a_3903_);
                if v_isShared_3906_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3905_, 0, v___x_3908_);
                    v___x_3910_ = v___x_3905_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
                    v___x_3910_ = v_reuseFailAlloc_3911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17___boxed(
    mut v_msg_3913_: *mut crate::leanh::LeanObject,
    mut v_declHint_3914_: *mut crate::leanh::LeanObject,
    mut v___y_3915_: *mut crate::leanh::LeanObject,
    mut v___y_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3918_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_3913_, v_declHint_3914_, v___y_3915_, v___y_3916_);
    crate::leanh::lean_dec(v___y_3916_);
    crate::leanh::lean_dec_ref(v___y_3915_);
    return v_res_3918_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(
    mut v_ref_3919_: *mut crate::leanh::LeanObject,
    mut v_msg_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3936_: u8 = 0;
    let mut v_cancelTk_x3f_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3938_: u8 = 0;
    let mut v_inheritedTraceOptions_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3924_ = crate::leanh::lean_ctor_get(v___y_3921_, 0);
    v_fileMap_3925_ = crate::leanh::lean_ctor_get(v___y_3921_, 1);
    v_options_3926_ = crate::leanh::lean_ctor_get(v___y_3921_, 2);
    v_currRecDepth_3927_ = crate::leanh::lean_ctor_get(v___y_3921_, 3);
    v_maxRecDepth_3928_ = crate::leanh::lean_ctor_get(v___y_3921_, 4);
    v_ref_3929_ = crate::leanh::lean_ctor_get(v___y_3921_, 5);
    v_currNamespace_3930_ = crate::leanh::lean_ctor_get(v___y_3921_, 6);
    v_openDecls_3931_ = crate::leanh::lean_ctor_get(v___y_3921_, 7);
    v_initHeartbeats_3932_ = crate::leanh::lean_ctor_get(v___y_3921_, 8);
    v_maxHeartbeats_3933_ = crate::leanh::lean_ctor_get(v___y_3921_, 9);
    v_quotContext_3934_ = crate::leanh::lean_ctor_get(v___y_3921_, 10);
    v_currMacroScope_3935_ = crate::leanh::lean_ctor_get(v___y_3921_, 11);
    v_diag_3936_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3921_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3937_ = crate::leanh::lean_ctor_get(v___y_3921_, 12);
    v_suppressElabErrors_3938_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3921_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3939_ = crate::leanh::lean_ctor_get(v___y_3921_, 13);
    v_ref_3940_ = l_Lean_replaceRef(v_ref_3919_, v_ref_3929_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3939_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3937_);
    crate::leanh::lean_inc(v_currMacroScope_3935_);
    crate::leanh::lean_inc(v_quotContext_3934_);
    crate::leanh::lean_inc(v_maxHeartbeats_3933_);
    crate::leanh::lean_inc(v_initHeartbeats_3932_);
    crate::leanh::lean_inc(v_openDecls_3931_);
    crate::leanh::lean_inc(v_currNamespace_3930_);
    crate::leanh::lean_inc(v_maxRecDepth_3928_);
    crate::leanh::lean_inc(v_currRecDepth_3927_);
    crate::leanh::lean_inc_ref(v_options_3926_);
    crate::leanh::lean_inc_ref(v_fileMap_3925_);
    crate::leanh::lean_inc_ref(v_fileName_3924_);
    v___x_3941_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3941_, 0, v_fileName_3924_);
    crate::leanh::lean_ctor_set(v___x_3941_, 1, v_fileMap_3925_);
    crate::leanh::lean_ctor_set(v___x_3941_, 2, v_options_3926_);
    crate::leanh::lean_ctor_set(v___x_3941_, 3, v_currRecDepth_3927_);
    crate::leanh::lean_ctor_set(v___x_3941_, 4, v_maxRecDepth_3928_);
    crate::leanh::lean_ctor_set(v___x_3941_, 5, v_ref_3940_);
    crate::leanh::lean_ctor_set(v___x_3941_, 6, v_currNamespace_3930_);
    crate::leanh::lean_ctor_set(v___x_3941_, 7, v_openDecls_3931_);
    crate::leanh::lean_ctor_set(v___x_3941_, 8, v_initHeartbeats_3932_);
    crate::leanh::lean_ctor_set(v___x_3941_, 9, v_maxHeartbeats_3933_);
    crate::leanh::lean_ctor_set(v___x_3941_, 10, v_quotContext_3934_);
    crate::leanh::lean_ctor_set(v___x_3941_, 11, v_currMacroScope_3935_);
    crate::leanh::lean_ctor_set(v___x_3941_, 12, v_cancelTk_x3f_3937_);
    crate::leanh::lean_ctor_set(v___x_3941_, 13, v_inheritedTraceOptions_3939_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3941_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3936_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3941_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3938_,
    );
    v___x_3942_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_3920_, v___x_3941_, v___y_3922_);
    crate::leanh::lean_dec_ref_known(v___x_3941_, 14);
    return v___x_3942_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(
    mut v_ref_3943_: *mut crate::leanh::LeanObject,
    mut v_msg_3944_: *mut crate::leanh::LeanObject,
    mut v___y_3945_: *mut crate::leanh::LeanObject,
    mut v___y_3946_: *mut crate::leanh::LeanObject,
    mut v___y_3947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3948_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_3943_, v_msg_3944_, v___y_3945_, v___y_3946_);
    crate::leanh::lean_dec(v___y_3946_);
    crate::leanh::lean_dec_ref(v___y_3945_);
    crate::leanh::lean_dec(v_ref_3943_);
    return v_res_3948_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(
    mut v_ref_3949_: *mut crate::leanh::LeanObject,
    mut v_msg_3950_: *mut crate::leanh::LeanObject,
    mut v_declHint_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3955_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_3950_, v_declHint_3951_, v___y_3952_, v___y_3953_);
    v_a_3956_ = crate::leanh::lean_ctor_get(v___x_3955_, 0);
    crate::leanh::lean_inc(v_a_3956_);
    crate::leanh::lean_dec_ref(v___x_3955_);
    v___x_3957_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_3949_, v_a_3956_, v___y_3952_, v___y_3953_);
    return v___x_3957_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(
    mut v_ref_3958_: *mut crate::leanh::LeanObject,
    mut v_msg_3959_: *mut crate::leanh::LeanObject,
    mut v_declHint_3960_: *mut crate::leanh::LeanObject,
    mut v___y_3961_: *mut crate::leanh::LeanObject,
    mut v___y_3962_: *mut crate::leanh::LeanObject,
    mut v___y_3963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3964_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_3958_, v_msg_3959_, v_declHint_3960_, v___y_3961_, v___y_3962_);
    crate::leanh::lean_dec(v___y_3962_);
    crate::leanh::lean_dec_ref(v___y_3961_);
    crate::leanh::lean_dec(v_ref_3958_);
    return v_res_3964_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3966_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0;
    v___x_3967_ = l_Lean_stringToMessageData(v___x_3966_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(
    mut v_ref_3968_: *mut crate::leanh::LeanObject,
    mut v_constName_3969_: *mut crate::leanh::LeanObject,
    mut v___y_3970_: *mut crate::leanh::LeanObject,
    mut v___y_3971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: u8 = 0;
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3973_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
    v___x_3974_ = 0;
    crate::leanh::lean_inc(v_constName_3969_);
    v___x_3975_ = l_Lean_MessageData_ofConstName(v_constName_3969_, v___x_3974_);
    v___x_3976_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3976_, 0, v___x_3973_);
    crate::leanh::lean_ctor_set(v___x_3976_, 1, v___x_3975_);
    v___x_3977_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once),
        _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3,
    );
    v___x_3978_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3978_, 0, v___x_3976_);
    crate::leanh::lean_ctor_set(v___x_3978_, 1, v___x_3977_);
    v___x_3979_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_3968_, v___x_3978_, v_constName_3969_, v___y_3970_, v___y_3971_);
    return v___x_3979_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(
    mut v_ref_3980_: *mut crate::leanh::LeanObject,
    mut v_constName_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3985_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_3980_, v_constName_3981_, v___y_3982_, v___y_3983_);
    crate::leanh::lean_dec(v___y_3983_);
    crate::leanh::lean_dec_ref(v___y_3982_);
    crate::leanh::lean_dec(v_ref_3980_);
    return v_res_3985_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(
    mut v_constName_3986_: *mut crate::leanh::LeanObject,
    mut v___y_3987_: *mut crate::leanh::LeanObject,
    mut v___y_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3990_ = crate::leanh::lean_ctor_get(v___y_3987_, 5);
    v___x_3991_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_3990_, v_constName_3986_, v___y_3987_, v___y_3988_);
    return v___x_3991_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(
    mut v_constName_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
    mut v___y_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3996_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_3992_, v___y_3993_, v___y_3994_);
    crate::leanh::lean_dec(v___y_3994_);
    crate::leanh::lean_dec_ref(v___y_3993_);
    return v_res_3996_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(
    mut v_constName_3997_: *mut crate::leanh::LeanObject,
    mut v___y_3998_: *mut crate::leanh::LeanObject,
    mut v___y_3999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: u8 = 0;
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4009_: u8 = 0;
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4001_ = lean_st_ref_get(v___y_3999_);
                v_env_4002_ = crate::leanh::lean_ctor_get(v___x_4001_, 0);
                crate::leanh::lean_inc_ref(v_env_4002_);
                crate::leanh::lean_dec(v___x_4001_);
                v___x_4003_ = 0;
                crate::leanh::lean_inc(v_constName_3997_);
                v___x_4004_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_4002_,
                    v_constName_3997_,
                    v___x_4003_,
                );
                if crate::leanh::lean_obj_tag(v___x_4004_) == 0 {
                    v___x_4005_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_3997_, v___y_3998_, v___y_3999_);
                    return v___x_4005_;
                } else {
                    crate::leanh::lean_dec(v_constName_3997_);
                    v_val_4006_ = crate::leanh::lean_ctor_get(v___x_4004_, 0);
                    v_isSharedCheck_4013_ = (!crate::leanh::lean_is_exclusive(v___x_4004_)) as u8;
                    if v_isSharedCheck_4013_ == 0 {
                        v___x_4008_ = v___x_4004_;
                        v_isShared_4009_ = v_isSharedCheck_4013_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4006_);
                        crate::leanh::lean_dec(v___x_4004_);
                        v___x_4008_ = crate::leanh::lean_box(0);
                        v_isShared_4009_ = v_isSharedCheck_4013_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4009_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4008_, 0);
                    v___x_4011_ = v___x_4008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4012_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_val_4006_);
                    v___x_4011_ = v_reuseFailAlloc_4012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8___boxed(
    mut v_constName_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
    mut v___y_4016_: *mut crate::leanh::LeanObject,
    mut v___y_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4018_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_4014_, v___y_4015_, v___y_4016_);
    crate::leanh::lean_dec(v___y_4016_);
    crate::leanh::lean_dec_ref(v___y_4015_);
    return v_res_4018_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(
    mut v_a_4019_: *mut crate::leanh::LeanObject,
    mut v_a_4020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4019_) == 0 {
                    v___x_4021_ = l_List_reverse___redArg(v_a_4020_);
                    return v___x_4021_;
                } else {
                    v_head_4022_ = crate::leanh::lean_ctor_get(v_a_4019_, 0);
                    v_tail_4023_ = crate::leanh::lean_ctor_get(v_a_4019_, 1);
                    v_isSharedCheck_4032_ = (!crate::leanh::lean_is_exclusive(v_a_4019_)) as u8;
                    if v_isSharedCheck_4032_ == 0 {
                        v___x_4025_ = v_a_4019_;
                        v_isShared_4026_ = v_isSharedCheck_4032_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4023_);
                        crate::leanh::lean_inc(v_head_4022_);
                        crate::leanh::lean_dec(v_a_4019_);
                        v___x_4025_ = crate::leanh::lean_box(0);
                        v_isShared_4026_ = v_isSharedCheck_4032_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4027_ = l_Lean_mkLevelParam(v_head_4022_);
                if v_isShared_4026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4025_, 1, v_a_4020_);
                    crate::leanh::lean_ctor_set(v___x_4025_, 0, v___x_4027_);
                    v___x_4029_ = v___x_4025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4031_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_a_4020_);
                    v___x_4029_ = v_reuseFailAlloc_4031_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4019_ = v_tail_4023_;
                v_a_4020_ = v___x_4029_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(
    mut v_constName_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v_levelParams_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4049_: u8 = 0;
    let mut v_a_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4053_: u8 = 0;
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_constName_4033_);
                v___x_4037_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_4033_, v___y_4034_, v___y_4035_);
                if crate::leanh::lean_obj_tag(v___x_4037_) == 0 {
                    v_a_4038_ = crate::leanh::lean_ctor_get(v___x_4037_, 0);
                    v_isSharedCheck_4049_ = (!crate::leanh::lean_is_exclusive(v___x_4037_)) as u8;
                    if v_isSharedCheck_4049_ == 0 {
                        v___x_4040_ = v___x_4037_;
                        v_isShared_4041_ = v_isSharedCheck_4049_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4038_);
                        crate::leanh::lean_dec(v___x_4037_);
                        v___x_4040_ = crate::leanh::lean_box(0);
                        v_isShared_4041_ = v_isSharedCheck_4049_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_constName_4033_);
                    v_a_4050_ = crate::leanh::lean_ctor_get(v___x_4037_, 0);
                    v_isSharedCheck_4057_ = (!crate::leanh::lean_is_exclusive(v___x_4037_)) as u8;
                    if v_isSharedCheck_4057_ == 0 {
                        v___x_4052_ = v___x_4037_;
                        v_isShared_4053_ = v_isSharedCheck_4057_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4050_);
                        crate::leanh::lean_dec(v___x_4037_);
                        v___x_4052_ = crate::leanh::lean_box(0);
                        v_isShared_4053_ = v_isSharedCheck_4057_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_4042_ = crate::leanh::lean_ctor_get(v_a_4038_, 1);
                crate::leanh::lean_inc(v_levelParams_4042_);
                crate::leanh::lean_dec(v_a_4038_);
                v___x_4043_ = crate::leanh::lean_box(0);
                v___x_4044_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_4042_, v___x_4043_);
                v___x_4045_ = l_Lean_mkConst(v_constName_4033_, v___x_4044_);
                if v_isShared_4041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4040_, 0, v___x_4045_);
                    v___x_4047_ = v___x_4040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4048_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4045_);
                    v___x_4047_ = v_reuseFailAlloc_4048_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4047_;
            }
            3 => {
                if v_isShared_4053_ == 0 {
                    v___x_4055_ = v___x_4052_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
                    v___x_4055_ = v_reuseFailAlloc_4056_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4___boxed(
    mut v_constName_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4062_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_4058_, v___y_4059_, v___y_4060_);
    crate::leanh::lean_dec(v___y_4060_);
    crate::leanh::lean_dec_ref(v___y_4059_);
    return v_res_4062_;
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(
    mut v_stx_4063_: *mut crate::leanh::LeanObject,
    mut v_n_4064_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
    mut v___y_4067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4069_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_4064_, v___y_4066_, v___y_4067_);
                if crate::leanh::lean_obj_tag(v___x_4069_) == 0 {
                    v_a_4070_ = crate::leanh::lean_ctor_get(v___x_4069_, 0);
                    crate::leanh::lean_inc(v_a_4070_);
                    crate::leanh::lean_dec_ref_known(v___x_4069_, 1);
                    v___x_4071_ = crate::leanh::lean_box(0);
                    v___x_4072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4072_, 0, v___x_4071_);
                    crate::leanh::lean_ctor_set(v___x_4072_, 1, v_stx_4063_);
                    v___x_4073_ = l_Lean_LocalContext_empty;
                    v___x_4074_ = 0;
                    v___x_4075_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_4075_, 0, v___x_4072_);
                    crate::leanh::lean_ctor_set(v___x_4075_, 1, v___x_4073_);
                    crate::leanh::lean_ctor_set(v___x_4075_, 2, v_expectedType_x3f_4065_);
                    crate::leanh::lean_ctor_set(v___x_4075_, 3, v_a_4070_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4075_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_4074_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4075_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                        v___x_4074_,
                    );
                    v___x_4076_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4076_, 0, v___x_4075_);
                    v___x_4077_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_4076_, v___y_4066_, v___y_4067_);
                    return v___x_4077_;
                } else {
                    crate::leanh::lean_dec(v_expectedType_x3f_4065_);
                    crate::leanh::lean_dec(v_stx_4063_);
                    v_a_4078_ = crate::leanh::lean_ctor_get(v___x_4069_, 0);
                    v_isSharedCheck_4085_ = (!crate::leanh::lean_is_exclusive(v___x_4069_)) as u8;
                    if v_isSharedCheck_4085_ == 0 {
                        v___x_4080_ = v___x_4069_;
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4078_);
                        crate::leanh::lean_dec(v___x_4069_);
                        v___x_4080_ = crate::leanh::lean_box(0);
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4081_ == 0 {
                    v___x_4083_ = v___x_4080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
                    v___x_4083_ = v_reuseFailAlloc_4084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1___boxed(
    mut v_stx_4086_: *mut crate::leanh::LeanObject,
    mut v_n_4087_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_4088_: *mut crate::leanh::LeanObject,
    mut v___y_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4092_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(
        v_stx_4086_,
        v_n_4087_,
        v_expectedType_x3f_4088_,
        v___y_4089_,
        v___y_4090_,
    );
    crate::leanh::lean_dec(v___y_4090_);
    crate::leanh::lean_dec_ref(v___y_4089_);
    return v_res_4092_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(
    mut v_keys_4093_: *mut crate::leanh::LeanObject,
    mut v_i_4094_: *mut crate::leanh::LeanObject,
    mut v_k_4095_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v_k_x27_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4096_ = lean_array_get_size(v_keys_4093_);
                v___x_4097_ = lean_nat_dec_lt(v_i_4094_, v___x_4096_);
                if v___x_4097_ == 0 {
                    crate::leanh::lean_dec(v_i_4094_);
                    return v___x_4097_;
                } else {
                    v_k_x27_4098_ = lean_array_fget_borrowed(v_keys_4093_, v_i_4094_);
                    v___x_4099_ = l_Lean_instBEqExtraModUse_beq(v_k_4095_, v_k_x27_4098_);
                    if v___x_4099_ == 0 {
                        v___x_4100_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4101_ = lean_nat_add(v_i_4094_, v___x_4100_);
                        crate::leanh::lean_dec(v_i_4094_);
                        v_i_4094_ = v___x_4101_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4094_);
                        return v___x_4099_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(
    mut v_keys_4103_: *mut crate::leanh::LeanObject,
    mut v_i_4104_: *mut crate::leanh::LeanObject,
    mut v_k_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4106_: u8 = 0;
    let mut v_r_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4106_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_4103_, v_i_4104_, v_k_4105_);
    crate::leanh::lean_dec_ref(v_k_4105_);
    crate::leanh::lean_dec_ref(v_keys_4103_);
    v_r_4107_ = crate::leanh::lean_box((v_res_4106_) as usize);
    return v_r_4107_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_4108_: usize = 0;
    let mut v___x_4109_: usize = 0;
    let mut v___x_4110_: usize = 0;
    v___x_4108_ = 5usize;
    v___x_4109_ = 1usize;
    v___x_4110_ = lean_usize_shift_left(v___x_4109_, v___x_4108_);
    return v___x_4110_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_4111_: usize = 0;
    let mut v___x_4112_: usize = 0;
    let mut v___x_4113_: usize = 0;
    v___x_4111_ = 1usize;
    v___x_4112_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
    v___x_4113_ = lean_usize_sub(v___x_4112_, v___x_4111_);
    return v___x_4113_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_x_4114_: *mut crate::leanh::LeanObject,
    mut v_x_4115_: usize,
    mut v_x_4116_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: usize = 0;
    let mut v___x_4120_: usize = 0;
    let mut v___x_4121_: usize = 0;
    let mut v_j_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v_node_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: usize = 0;
    let mut v___x_4129_: u8 = 0;
    let mut v_ks_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4114_) == 0 {
                    v_es_4117_ = crate::leanh::lean_ctor_get(v_x_4114_, 0);
                    v___x_4118_ = crate::leanh::lean_box(2);
                    v___x_4119_ = 5usize;
                    v___x_4120_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_4121_ = lean_usize_land(v_x_4115_, v___x_4120_);
                    v_j_4122_ = lean_usize_to_nat(v___x_4121_);
                    v___x_4123_ = lean_array_get_borrowed(v___x_4118_, v_es_4117_, v_j_4122_);
                    crate::leanh::lean_dec(v_j_4122_);
                    match crate::leanh::lean_obj_tag(v___x_4123_) {
                        0 => {
                            v_key_4124_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                            v___x_4125_ = l_Lean_instBEqExtraModUse_beq(v_x_4116_, v_key_4124_);
                            return v___x_4125_;
                        }
                        1 => {
                            v_node_4126_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                            v___x_4127_ = lean_usize_shift_right(v_x_4115_, v___x_4119_);
                            v_x_4114_ = v_node_4126_;
                            v_x_4115_ = v___x_4127_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4129_ = 0;
                            return v___x_4129_;
                        }
                    }
                } else {
                    v_ks_4130_ = crate::leanh::lean_ctor_get(v_x_4114_, 0);
                    v___x_4131_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4132_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_4130_, v___x_4131_, v_x_4116_);
                    return v___x_4132_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_4133_: *mut crate::leanh::LeanObject,
    mut v_x_4134_: *mut crate::leanh::LeanObject,
    mut v_x_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6766__boxed_4136_: usize = 0;
    let mut v_res_4137_: u8 = 0;
    let mut v_r_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6766__boxed_4136_ = crate::leanh::lean_unbox_usize(v_x_4134_);
    crate::leanh::lean_dec(v_x_4134_);
    v_res_4137_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4133_, v_x_6766__boxed_4136_, v_x_4135_);
    crate::leanh::lean_dec_ref(v_x_4135_);
    crate::leanh::lean_dec_ref(v_x_4133_);
    v_r_4138_ = crate::leanh::lean_box((v_res_4137_) as usize);
    return v_r_4138_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(
    mut v_x_4139_: *mut crate::leanh::LeanObject,
    mut v_x_4140_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4141_: u64 = 0;
    let mut v___x_4142_: usize = 0;
    let mut v___x_4143_: u8 = 0;
    v___x_4141_ = l_Lean_instHashableExtraModUse_hash(v_x_4140_);
    v___x_4142_ = lean_uint64_to_usize(v___x_4141_);
    v___x_4143_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4139_, v___x_4142_, v_x_4140_);
    return v___x_4143_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4144_: *mut crate::leanh::LeanObject,
    mut v_x_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4146_: u8 = 0;
    let mut v_r_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4146_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_4144_, v_x_4145_);
    crate::leanh::lean_dec_ref(v_x_4145_);
    crate::leanh::lean_dec_ref(v_x_4144_);
    v_r_4147_ = crate::leanh::lean_box((v_res_4146_) as usize);
    return v_r_4147_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0()
-> f64 {
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: f64 = 0.0;
    v___x_4148_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4149_ = lean_float_of_nat(v___x_4148_);
    return v___x_4149_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(
    mut v_cls_4153_: *mut crate::leanh::LeanObject,
    mut v_msg_4154_: *mut crate::leanh::LeanObject,
    mut v___y_4155_: *mut crate::leanh::LeanObject,
    mut v___y_4156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4163_: u8 = 0;
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v_tid_4177_: u64 = 0;
    let mut v_traces_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4181_: u8 = 0;
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: f64 = 0.0;
    let mut v___x_4184_: u8 = 0;
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4158_ = crate::leanh::lean_ctor_get(v___y_4155_, 5);
                v___x_4159_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_4154_, v___y_4155_, v___y_4156_);
                v_a_4160_ = crate::leanh::lean_ctor_get(v___x_4159_, 0);
                v_isSharedCheck_4204_ = (!crate::leanh::lean_is_exclusive(v___x_4159_)) as u8;
                if v_isSharedCheck_4204_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    v_isShared_4163_ = v_isSharedCheck_4204_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4160_);
                    crate::leanh::lean_dec(v___x_4159_);
                    v___x_4162_ = crate::leanh::lean_box(0);
                    v_isShared_4163_ = v_isSharedCheck_4204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4164_ = lean_st_ref_take(v___y_4156_);
                v_traceState_4165_ = crate::leanh::lean_ctor_get(v___x_4164_, 4);
                v_env_4166_ = crate::leanh::lean_ctor_get(v___x_4164_, 0);
                v_nextMacroScope_4167_ = crate::leanh::lean_ctor_get(v___x_4164_, 1);
                v_ngen_4168_ = crate::leanh::lean_ctor_get(v___x_4164_, 2);
                v_auxDeclNGen_4169_ = crate::leanh::lean_ctor_get(v___x_4164_, 3);
                v_cache_4170_ = crate::leanh::lean_ctor_get(v___x_4164_, 5);
                v_messages_4171_ = crate::leanh::lean_ctor_get(v___x_4164_, 6);
                v_infoState_4172_ = crate::leanh::lean_ctor_get(v___x_4164_, 7);
                v_snapshotTasks_4173_ = crate::leanh::lean_ctor_get(v___x_4164_, 8);
                v_isSharedCheck_4203_ = (!crate::leanh::lean_is_exclusive(v___x_4164_)) as u8;
                if v_isSharedCheck_4203_ == 0 {
                    v___x_4175_ = v___x_4164_;
                    v_isShared_4176_ = v_isSharedCheck_4203_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4173_);
                    crate::leanh::lean_inc(v_infoState_4172_);
                    crate::leanh::lean_inc(v_messages_4171_);
                    crate::leanh::lean_inc(v_cache_4170_);
                    crate::leanh::lean_inc(v_traceState_4165_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4169_);
                    crate::leanh::lean_inc(v_ngen_4168_);
                    crate::leanh::lean_inc(v_nextMacroScope_4167_);
                    crate::leanh::lean_inc(v_env_4166_);
                    crate::leanh::lean_dec(v___x_4164_);
                    v___x_4175_ = crate::leanh::lean_box(0);
                    v_isShared_4176_ = v_isSharedCheck_4203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4177_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4178_ = crate::leanh::lean_ctor_get(v_traceState_4165_, 0);
                v_isSharedCheck_4202_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4165_)) as u8;
                if v_isSharedCheck_4202_ == 0 {
                    v___x_4180_ = v_traceState_4165_;
                    v_isShared_4181_ = v_isSharedCheck_4202_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4178_);
                    crate::leanh::lean_dec(v_traceState_4165_);
                    v___x_4180_ = crate::leanh::lean_box(0);
                    v_isShared_4181_ = v_isSharedCheck_4202_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4182_ = crate::leanh::lean_box(0);
                v___x_4183_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
                v___x_4184_ = 0;
                v___x_4185_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1;
                v___x_4186_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4186_, 0, v_cls_4153_);
                crate::leanh::lean_ctor_set(v___x_4186_, 1, v___x_4182_);
                crate::leanh::lean_ctor_set(v___x_4186_, 2, v___x_4185_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4186_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4183_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4186_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4183_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4186_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4184_,
                );
                v___x_4187_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2;
                v___x_4188_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4188_, 0, v___x_4186_);
                crate::leanh::lean_ctor_set(v___x_4188_, 1, v_a_4160_);
                crate::leanh::lean_ctor_set(v___x_4188_, 2, v___x_4187_);
                crate::leanh::lean_inc(v_ref_4158_);
                v___x_4189_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4189_, 0, v_ref_4158_);
                crate::leanh::lean_ctor_set(v___x_4189_, 1, v___x_4188_);
                v___x_4190_ = l_Lean_PersistentArray_push___redArg(v_traces_4178_, v___x_4189_);
                if v_isShared_4181_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4180_, 0, v___x_4190_);
                    v___x_4192_ = v___x_4180_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4190_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4201_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4177_,
                    );
                    v___x_4192_ = v_reuseFailAlloc_4201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4175_, 4, v___x_4192_);
                    v___x_4194_ = v___x_4175_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4200_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_env_4166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_nextMacroScope_4167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 2, v_ngen_4168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 3, v_auxDeclNGen_4169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 4, v___x_4192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 5, v_cache_4170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 6, v_messages_4171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 7, v_infoState_4172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 8, v_snapshotTasks_4173_);
                    v___x_4194_ = v_reuseFailAlloc_4200_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4195_ = lean_st_ref_set(v___y_4156_, v___x_4194_);
                v___x_4196_ = crate::leanh::lean_box(0);
                if v_isShared_4163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4162_, 0, v___x_4196_);
                    v___x_4198_ = v___x_4162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4199_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4196_);
                    v___x_4198_ = v_reuseFailAlloc_4199_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___boxed(
    mut v_cls_4205_: *mut crate::leanh::LeanObject,
    mut v_msg_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
    mut v___y_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4210_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_4205_, v_msg_4206_, v___y_4207_, v___y_4208_);
    crate::leanh::lean_dec(v___y_4208_);
    crate::leanh::lean_dec_ref(v___y_4207_);
    return v_res_4210_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4213_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1;
    v___x_4214_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0;
    v___x_4215_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4214_,
        v___x_4213_,
    );
    return v___x_4215_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4216_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4216_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3);
    v___x_4218_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4218_, 0, v___x_4217_);
    return v___x_4218_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4219_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4);
    v___x_4220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4220_, 0, v___x_4219_);
    crate::leanh::lean_ctor_set(v___x_4220_, 1, v___x_4219_);
    return v___x_4220_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4225_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8;
    v___x_4226_ = l_Lean_stringToMessageData(v___x_4225_);
    return v___x_4226_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4228_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10;
    v___x_4229_ = l_Lean_stringToMessageData(v___x_4228_);
    return v___x_4229_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1;
    v___x_4231_ = l_Lean_stringToMessageData(v___x_4230_);
    return v___x_4231_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_4235_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7;
    v___x_4236_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14;
    v___x_4237_ = l_Lean_Name_append(v___x_4236_, v_cls_4235_);
    return v___x_4237_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4239_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16;
    v___x_4240_ = l_Lean_stringToMessageData(v___x_4239_);
    return v___x_4240_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18;
    v___x_4243_ = l_Lean_stringToMessageData(v___x_4242_);
    return v___x_4243_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(
    mut v_mod_4248_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4249_: u8,
    mut v_hint_4250_: *mut crate::leanh::LeanObject,
    mut v___y_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4256_: u8 = 0;
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v_asyncMode_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_unused_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: u8 = 0;
    let mut v_options_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4293_: u8 = 0;
    let mut v_inheritedTraceOptions_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u8 = 0;
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: u8 = 0;
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4254_ = lean_st_ref_get(v___y_4252_);
                v_env_4255_ = crate::leanh::lean_ctor_get(v___x_4254_, 0);
                crate::leanh::lean_inc_ref(v_env_4255_);
                crate::leanh::lean_dec(v___x_4254_);
                v_isExporting_4256_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_4255_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_4255_);
                v___x_4257_ = lean_st_ref_get(v___y_4252_);
                v_env_4258_ = crate::leanh::lean_ctor_get(v___x_4257_, 0);
                crate::leanh::lean_inc_ref(v_env_4258_);
                crate::leanh::lean_dec(v___x_4257_);
                v___x_4259_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
                crate::leanh::lean_inc(v_mod_4248_);
                v_entry_4260_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_4260_, 0, v_mod_4248_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4260_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_4256_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4260_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4249_,
                );
                v___x_4261_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_4262_ = crate::leanh::lean_box(1);
                v___x_4263_ = crate::leanh::lean_box(0);
                v___x_4290_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4259_,
                    v___x_4261_,
                    v_env_4258_,
                    v___x_4262_,
                    v___x_4263_,
                );
                v___x_4291_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_4290_, v_entry_4260_);
                crate::leanh::lean_dec(v___x_4290_);
                if v___x_4291_ == 0 {
                    v_options_4292_ = crate::leanh::lean_ctor_get(v___y_4251_, 2);
                    v_hasTrace_4293_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4292_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4293_ == 0 {
                        crate::leanh::lean_dec(v_hint_4250_);
                        crate::leanh::lean_dec(v_mod_4248_);
                        v___y_4265_ = v___y_4252_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4294_ =
                            crate::leanh::lean_ctor_get(v___y_4251_, 13);
                        v_cls_4295_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7;
                        v___x_4315_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15);
                        v___x_4316_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4294_,
                            v_options_4292_,
                            v___x_4315_,
                        );
                        if v___x_4316_ == 0 {
                            crate::leanh::lean_dec(v_hint_4250_);
                            crate::leanh::lean_dec(v_mod_4248_);
                            v___y_4265_ = v___y_4252_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4317_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17);
                            if v_isExporting_4256_ == 0 {
                                v___x_4326_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22;
                                v___y_4319_ = v___x_4326_;
                                state = 6;
                                continue;
                            } else {
                                v___x_4327_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23;
                                v___y_4319_ = v___x_4327_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4260_, 1);
                    crate::leanh::lean_dec(v_hint_4250_);
                    crate::leanh::lean_dec(v_mod_4248_);
                    v___x_4328_ = crate::leanh::lean_box(0);
                    v___x_4329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4329_, 0, v___x_4328_);
                    return v___x_4329_;
                }
            }
            1 => {
                v___x_4266_ = lean_st_ref_take(v___y_4265_);
                v_toEnvExtension_4267_ = crate::leanh::lean_ctor_get(v___x_4261_, 0);
                v_env_4268_ = crate::leanh::lean_ctor_get(v___x_4266_, 0);
                v_nextMacroScope_4269_ = crate::leanh::lean_ctor_get(v___x_4266_, 1);
                v_ngen_4270_ = crate::leanh::lean_ctor_get(v___x_4266_, 2);
                v_auxDeclNGen_4271_ = crate::leanh::lean_ctor_get(v___x_4266_, 3);
                v_traceState_4272_ = crate::leanh::lean_ctor_get(v___x_4266_, 4);
                v_messages_4273_ = crate::leanh::lean_ctor_get(v___x_4266_, 6);
                v_infoState_4274_ = crate::leanh::lean_ctor_get(v___x_4266_, 7);
                v_snapshotTasks_4275_ = crate::leanh::lean_ctor_get(v___x_4266_, 8);
                v_isSharedCheck_4288_ = (!crate::leanh::lean_is_exclusive(v___x_4266_)) as u8;
                if v_isSharedCheck_4288_ == 0 {
                    v_unused_4289_ = crate::leanh::lean_ctor_get(v___x_4266_, 5);
                    crate::leanh::lean_dec(v_unused_4289_);
                    v___x_4277_ = v___x_4266_;
                    v_isShared_4278_ = v_isSharedCheck_4288_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4275_);
                    crate::leanh::lean_inc(v_infoState_4274_);
                    crate::leanh::lean_inc(v_messages_4273_);
                    crate::leanh::lean_inc(v_traceState_4272_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4271_);
                    crate::leanh::lean_inc(v_ngen_4270_);
                    crate::leanh::lean_inc(v_nextMacroScope_4269_);
                    crate::leanh::lean_inc(v_env_4268_);
                    crate::leanh::lean_dec(v___x_4266_);
                    v___x_4277_ = crate::leanh::lean_box(0);
                    v_isShared_4278_ = v_isSharedCheck_4288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4279_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4267_, 2);
                v___x_4280_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4261_,
                    v_env_4268_,
                    v_entry_4260_,
                    v_asyncMode_4279_,
                    v___x_4263_,
                );
                v___x_4281_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5);
                if v_isShared_4278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4277_, 5, v___x_4281_);
                    crate::leanh::lean_ctor_set(v___x_4277_, 0, v___x_4280_);
                    v___x_4283_ = v___x_4277_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4287_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_nextMacroScope_4269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 2, v_ngen_4270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 3, v_auxDeclNGen_4271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 4, v_traceState_4272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 5, v___x_4281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 6, v_messages_4273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 7, v_infoState_4274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4287_, 8, v_snapshotTasks_4275_);
                    v___x_4283_ = v_reuseFailAlloc_4287_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4284_ = lean_st_ref_set(v___y_4265_, v___x_4283_);
                v___x_4285_ = crate::leanh::lean_box(0);
                v___x_4286_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4286_, 0, v___x_4285_);
                return v___x_4286_;
            }
            4 => {
                v___x_4299_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4299_, 0, v___y_4297_);
                crate::leanh::lean_ctor_set(v___x_4299_, 1, v___y_4298_);
                v___x_4300_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_4295_, v___x_4299_, v___y_4251_, v___y_4252_);
                if crate::leanh::lean_obj_tag(v___x_4300_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4300_, 1);
                    v___y_4265_ = v___y_4252_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4260_, 1);
                    return v___x_4300_;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_4303_);
                v___x_4304_ = l_Lean_stringToMessageData(v___y_4303_);
                v___x_4305_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4305_, 0, v___y_4302_);
                crate::leanh::lean_ctor_set(v___x_4305_, 1, v___x_4304_);
                v___x_4306_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
                v___x_4307_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4307_, 0, v___x_4305_);
                crate::leanh::lean_ctor_set(v___x_4307_, 1, v___x_4306_);
                v___x_4308_ = l_Lean_MessageData_ofName(v_mod_4248_);
                v___x_4309_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4309_, 0, v___x_4307_);
                crate::leanh::lean_ctor_set(v___x_4309_, 1, v___x_4308_);
                v___x_4310_ = l_Lean_Name_isAnonymous(v_hint_4250_);
                if v___x_4310_ == 0 {
                    v___x_4311_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11);
                    v___x_4312_ = l_Lean_MessageData_ofName(v_hint_4250_);
                    v___x_4313_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4313_, 0, v___x_4311_);
                    crate::leanh::lean_ctor_set(v___x_4313_, 1, v___x_4312_);
                    v___y_4297_ = v___x_4309_;
                    v___y_4298_ = v___x_4313_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_4250_);
                    v___x_4314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
                    v___y_4297_ = v___x_4309_;
                    v___y_4298_ = v___x_4314_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_4319_);
                v___x_4320_ = l_Lean_stringToMessageData(v___y_4319_);
                v___x_4321_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4321_, 0, v___x_4317_);
                crate::leanh::lean_ctor_set(v___x_4321_, 1, v___x_4320_);
                v___x_4322_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
                v___x_4323_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4321_);
                crate::leanh::lean_ctor_set(v___x_4323_, 1, v___x_4322_);
                if v_isMeta_4249_ == 0 {
                    v___x_4324_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20;
                    v___y_4302_ = v___x_4323_;
                    v___y_4303_ = v___x_4324_;
                    state = 5;
                    continue;
                } else {
                    v___x_4325_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21;
                    v___y_4302_ = v___x_4323_;
                    v___y_4303_ = v___x_4325_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___boxed(
    mut v_mod_4330_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4331_: *mut crate::leanh::LeanObject,
    mut v_hint_4332_: *mut crate::leanh::LeanObject,
    mut v___y_4333_: *mut crate::leanh::LeanObject,
    mut v___y_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_4336_: u8 = 0;
    let mut v_res_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4336_ = (crate::leanh::lean_unbox(v_isMeta_4331_) as u8);
    v_res_4337_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_4330_, v_isMeta_boxed_4336_, v_hint_4332_, v___y_4333_, v___y_4334_);
    crate::leanh::lean_dec(v___y_4334_);
    crate::leanh::lean_dec_ref(v___y_4333_);
    return v_res_4337_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(
    mut v___x_4338_: *mut crate::leanh::LeanObject,
    mut v_declName_4339_: *mut crate::leanh::LeanObject,
    mut v_as_4340_: *mut crate::leanh::LeanObject,
    mut v_sz_4341_: usize,
    mut v_i_4342_: usize,
    mut v_b_4343_: *mut crate::leanh::LeanObject,
    mut v___y_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4347_: u8 = 0;
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: usize = 0;
    let mut v___x_4360_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4347_ = lean_usize_dec_lt(v_i_4342_, v_sz_4341_);
                if v___x_4347_ == 0 {
                    crate::leanh::lean_dec(v_declName_4339_);
                    v___x_4348_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4348_, 0, v_b_4343_);
                    return v___x_4348_;
                } else {
                    v___x_4349_ = l_Lean_Environment_header(v___x_4338_);
                    v_modules_4350_ = crate::leanh::lean_ctor_get(v___x_4349_, 3);
                    crate::leanh::lean_inc_ref(v_modules_4350_);
                    crate::leanh::lean_dec_ref(v___x_4349_);
                    v___x_4351_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_4352_ = lean_array_uget_borrowed(v_as_4340_, v_i_4342_);
                    v___x_4353_ = lean_array_get(v___x_4351_, v_modules_4350_, v_a_4352_);
                    crate::leanh::lean_dec_ref(v_modules_4350_);
                    v_toImport_4354_ = crate::leanh::lean_ctor_get(v___x_4353_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_4354_);
                    crate::leanh::lean_dec(v___x_4353_);
                    v_module_4355_ = crate::leanh::lean_ctor_get(v_toImport_4354_, 0);
                    crate::leanh::lean_inc(v_module_4355_);
                    crate::leanh::lean_dec_ref(v_toImport_4354_);
                    v___x_4356_ = 0;
                    crate::leanh::lean_inc(v_declName_4339_);
                    v___x_4357_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_4355_, v___x_4356_, v_declName_4339_, v___y_4344_, v___y_4345_);
                    if crate::leanh::lean_obj_tag(v___x_4357_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4357_, 1);
                        v___x_4358_ = crate::leanh::lean_box(0);
                        v___x_4359_ = 1usize;
                        v___x_4360_ = lean_usize_add(v_i_4342_, v___x_4359_);
                        v_i_4342_ = v___x_4360_;
                        v_b_4343_ = v___x_4358_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_4339_);
                        return v___x_4357_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(
    mut v___x_4362_: *mut crate::leanh::LeanObject,
    mut v_declName_4363_: *mut crate::leanh::LeanObject,
    mut v_as_4364_: *mut crate::leanh::LeanObject,
    mut v_sz_4365_: *mut crate::leanh::LeanObject,
    mut v_i_4366_: *mut crate::leanh::LeanObject,
    mut v_b_4367_: *mut crate::leanh::LeanObject,
    mut v___y_4368_: *mut crate::leanh::LeanObject,
    mut v___y_4369_: *mut crate::leanh::LeanObject,
    mut v___y_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4371_: usize = 0;
    let mut v_i_boxed_4372_: usize = 0;
    let mut v_res_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4371_ = crate::leanh::lean_unbox_usize(v_sz_4365_);
    crate::leanh::lean_dec(v_sz_4365_);
    v_i_boxed_4372_ = crate::leanh::lean_unbox_usize(v_i_4366_);
    crate::leanh::lean_dec(v_i_4366_);
    v_res_4373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_4362_, v_declName_4363_, v_as_4364_, v_sz_boxed_4371_, v_i_boxed_4372_, v_b_4367_, v___y_4368_, v___y_4369_);
    crate::leanh::lean_dec(v___y_4369_);
    crate::leanh::lean_dec_ref(v___y_4368_);
    crate::leanh::lean_dec_ref(v_as_4364_);
    crate::leanh::lean_dec_ref(v___x_4362_);
    return v_res_4373_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_x_4375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4375_) == 0 {
                    v___x_4376_ = crate::leanh::lean_box(0);
                    return v___x_4376_;
                } else {
                    v_key_4377_ = crate::leanh::lean_ctor_get(v_x_4375_, 0);
                    v_value_4378_ = crate::leanh::lean_ctor_get(v_x_4375_, 1);
                    v_tail_4379_ = crate::leanh::lean_ctor_get(v_x_4375_, 2);
                    v___x_4380_ = lean_name_eq(v_key_4377_, v_a_4374_);
                    if v___x_4380_ == 0 {
                        v_x_4375_ = v_tail_4379_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4378_);
                        v___x_4382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4382_, 0, v_value_4378_);
                        return v___x_4382_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_a_4383_: *mut crate::leanh::LeanObject,
    mut v_x_4384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4385_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_4383_, v_x_4384_);
    crate::leanh::lean_dec(v_x_4384_);
    crate::leanh::lean_dec(v_a_4383_);
    return v_res_4385_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u64 = 0;
    v___x_4386_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4387_ = lean_uint64_of_nat(v___x_4386_);
    return v___x_4387_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(
    mut v_m_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4393_: u64 = 0;
    let mut v___x_4394_: u64 = 0;
    let mut v___x_4395_: u64 = 0;
    let mut v_fold_4396_: u64 = 0;
    let mut v___x_4397_: u64 = 0;
    let mut v___x_4398_: u64 = 0;
    let mut v___x_4399_: u64 = 0;
    let mut v___x_4400_: usize = 0;
    let mut v___x_4401_: usize = 0;
    let mut v___x_4402_: usize = 0;
    let mut v___x_4403_: usize = 0;
    let mut v___x_4404_: usize = 0;
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: u64 = 0;
    let mut v_hash_4408_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4390_ = crate::leanh::lean_ctor_get(v_m_4388_, 1);
                v___x_4391_ = lean_array_get_size(v_buckets_4390_);
                if crate::leanh::lean_obj_tag(v_a_4389_) == 0 {
                    v___x_4407_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0);
                    v___y_4393_ = v___x_4407_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4408_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_4389_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4393_ = v_hash_4408_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4394_ = 32u64;
                v___x_4395_ = lean_uint64_shift_right(v___y_4393_, v___x_4394_);
                v_fold_4396_ = lean_uint64_xor(v___y_4393_, v___x_4395_);
                v___x_4397_ = 16u64;
                v___x_4398_ = lean_uint64_shift_right(v_fold_4396_, v___x_4397_);
                v___x_4399_ = lean_uint64_xor(v_fold_4396_, v___x_4398_);
                v___x_4400_ = lean_uint64_to_usize(v___x_4399_);
                v___x_4401_ = lean_usize_of_nat(v___x_4391_);
                v___x_4402_ = 1usize;
                v___x_4403_ = lean_usize_sub(v___x_4401_, v___x_4402_);
                v___x_4404_ = lean_usize_land(v___x_4400_, v___x_4403_);
                v___x_4405_ = lean_array_uget_borrowed(v_buckets_4390_, v___x_4404_);
                v___x_4406_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_4389_, v___x_4405_);
                return v___x_4406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___boxed(
    mut v_m_4409_: *mut crate::leanh::LeanObject,
    mut v_a_4410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4411_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_4409_, v_a_4410_);
    crate::leanh::lean_dec(v_a_4410_);
    crate::leanh::lean_dec_ref(v_m_4409_);
    return v_res_4411_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4414_ =
        l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1;
    v___x_4415_ =
        l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0;
    v___x_4416_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4415_,
        v___x_4414_,
    );
    return v___x_4416_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(
    mut v_declName_4419_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4420_: u8,
    mut v___y_4421_: *mut crate::leanh::LeanObject,
    mut v___y_4422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4432_: usize = 0;
    let mut v___x_4433_: usize = 0;
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4441_: u8 = 0;
    let mut v_unused_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4454_: u8 = 0;
    let mut v_toImport_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v___x_4466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4424_ = lean_st_ref_get(v___y_4422_);
                v_env_4428_ = crate::leanh::lean_ctor_get(v___x_4424_, 0);
                crate::leanh::lean_inc_ref(v_env_4428_);
                crate::leanh::lean_dec(v___x_4424_);
                v___x_4443_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4428_, v_declName_4419_);
                if crate::leanh::lean_obj_tag(v___x_4443_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_4428_);
                    crate::leanh::lean_dec(v_declName_4419_);
                    state = 1;
                    continue;
                } else {
                    v_val_4444_ = crate::leanh::lean_ctor_get(v___x_4443_, 0);
                    crate::leanh::lean_inc(v_val_4444_);
                    crate::leanh::lean_dec_ref_known(v___x_4443_, 1);
                    v___x_4445_ = l_Lean_Environment_header(v_env_4428_);
                    v_modules_4446_ = crate::leanh::lean_ctor_get(v___x_4445_, 3);
                    crate::leanh::lean_inc_ref(v_modules_4446_);
                    crate::leanh::lean_dec_ref(v___x_4445_);
                    v___x_4447_ = lean_array_get_size(v_modules_4446_);
                    v___x_4448_ = lean_nat_dec_lt(v_val_4444_, v___x_4447_);
                    if v___x_4448_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_4446_);
                        crate::leanh::lean_dec(v_val_4444_);
                        crate::leanh::lean_dec_ref(v_env_4428_);
                        crate::leanh::lean_dec(v_declName_4419_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4449_ = lean_st_ref_get(v___y_4422_);
                        v_env_4450_ = crate::leanh::lean_ctor_get(v___x_4449_, 0);
                        crate::leanh::lean_inc_ref(v_env_4450_);
                        crate::leanh::lean_dec(v___x_4449_);
                        v___x_4451_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2);
                        v___x_4452_ = lean_array_fget(v_modules_4446_, v_val_4444_);
                        crate::leanh::lean_dec(v_val_4444_);
                        crate::leanh::lean_dec_ref(v_modules_4446_);
                        if v_isMeta_4420_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_4450_);
                            v___y_4454_ = v_isMeta_4420_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_4419_);
                            v___x_4465_ = l_Lean_isMarkedMeta(v_env_4450_, v_declName_4419_);
                            if v___x_4465_ == 0 {
                                v___y_4454_ = v_isMeta_4420_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4466_ = 0;
                                v___y_4454_ = v___x_4466_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4426_ = crate::leanh::lean_box(0);
                v___x_4427_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4427_, 0, v___x_4426_);
                return v___x_4427_;
            }
            2 => {
                v___x_4431_ = crate::leanh::lean_box(0);
                v_sz_4432_ = lean_array_size(v___y_4430_);
                v___x_4433_ = 0usize;
                v___x_4434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_4428_, v_declName_4419_, v___y_4430_, v_sz_4432_, v___x_4433_, v___x_4431_, v___y_4421_, v___y_4422_);
                crate::leanh::lean_dec_ref(v___y_4430_);
                crate::leanh::lean_dec_ref(v_env_4428_);
                if crate::leanh::lean_obj_tag(v___x_4434_) == 0 {
                    v_isSharedCheck_4441_ = (!crate::leanh::lean_is_exclusive(v___x_4434_)) as u8;
                    if v_isSharedCheck_4441_ == 0 {
                        v_unused_4442_ = crate::leanh::lean_ctor_get(v___x_4434_, 0);
                        crate::leanh::lean_dec(v_unused_4442_);
                        v___x_4436_ = v___x_4434_;
                        v_isShared_4437_ = v_isSharedCheck_4441_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4434_);
                        v___x_4436_ = crate::leanh::lean_box(0);
                        v_isShared_4437_ = v_isSharedCheck_4441_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4434_;
                }
            }
            3 => {
                if v_isShared_4437_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4436_, 0, v___x_4431_);
                    v___x_4439_ = v___x_4436_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4431_);
                    v___x_4439_ = v_reuseFailAlloc_4440_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4439_;
            }
            5 => {
                v_toImport_4455_ = crate::leanh::lean_ctor_get(v___x_4452_, 0);
                crate::leanh::lean_inc_ref(v_toImport_4455_);
                crate::leanh::lean_dec(v___x_4452_);
                v_module_4456_ = crate::leanh::lean_ctor_get(v_toImport_4455_, 0);
                crate::leanh::lean_inc(v_module_4456_);
                crate::leanh::lean_dec_ref(v_toImport_4455_);
                crate::leanh::lean_inc(v_declName_4419_);
                v___x_4457_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_4456_, v___y_4454_, v_declName_4419_, v___y_4421_, v___y_4422_);
                if crate::leanh::lean_obj_tag(v___x_4457_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4457_, 1);
                    v___x_4458_ = l_Lean_indirectModUseExt;
                    v___x_4459_ = crate::leanh::lean_box(1);
                    v___x_4460_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_4428_);
                    v___x_4461_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4451_,
                        v___x_4458_,
                        v_env_4428_,
                        v___x_4459_,
                        v___x_4460_,
                    );
                    v___x_4462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_4461_, v_declName_4419_);
                    crate::leanh::lean_dec(v___x_4461_);
                    if crate::leanh::lean_obj_tag(v___x_4462_) == 0 {
                        v___x_4463_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3;
                        v___y_4430_ = v___x_4463_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4464_ = crate::leanh::lean_ctor_get(v___x_4462_, 0);
                        crate::leanh::lean_inc(v_val_4464_);
                        crate::leanh::lean_dec_ref_known(v___x_4462_, 1);
                        v___y_4430_ = v_val_4464_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_4428_);
                    crate::leanh::lean_dec(v_declName_4419_);
                    return v___x_4457_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(
    mut v_declName_4467_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4468_: *mut crate::leanh::LeanObject,
    mut v___y_4469_: *mut crate::leanh::LeanObject,
    mut v___y_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_4472_: u8 = 0;
    let mut v_res_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4472_ = (crate::leanh::lean_unbox(v_isMeta_4468_) as u8);
    v_res_4473_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(
        v_declName_4467_,
        v_isMeta_boxed_4472_,
        v___y_4469_,
        v___y_4470_,
    );
    crate::leanh::lean_dec(v___y_4470_);
    crate::leanh::lean_dec_ref(v___y_4469_);
    return v_res_4473_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg___lam__1(
    mut v_parserNamespace_4474_: *mut crate::leanh::LeanObject,
    mut v_x_4475_: u8,
    mut v_stx_4476_: *mut crate::leanh::LeanObject,
    mut v___y_4477_: *mut crate::leanh::LeanObject,
    mut v___y_4478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4484_: u8 = 0;
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: u8 = 0;
    let mut v___x_4488_: u8 = 0;
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: u8 = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4499_: u8 = 0;
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_unused_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_unused_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4528_: u8 = 0;
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v_isSharedCheck_4533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_stx_4476_);
                v___x_4480_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(
                    v_parserNamespace_4474_,
                    v_stx_4476_,
                    v___y_4477_,
                    v___y_4478_,
                );
                if crate::leanh::lean_obj_tag(v___x_4480_) == 0 {
                    v_a_4481_ = crate::leanh::lean_ctor_get(v___x_4480_, 0);
                    v_isSharedCheck_4533_ = (!crate::leanh::lean_is_exclusive(v___x_4480_)) as u8;
                    if v_isSharedCheck_4533_ == 0 {
                        v___x_4483_ = v___x_4480_;
                        v_isShared_4484_ = v_isSharedCheck_4533_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4481_);
                        crate::leanh::lean_dec(v___x_4480_);
                        v___x_4483_ = crate::leanh::lean_box(0);
                        v_isShared_4484_ = v_isSharedCheck_4533_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_4476_);
                    return v___x_4480_;
                }
            }
            1 => {
                v___x_4485_ = lean_st_ref_get(v___y_4478_);
                v_env_4486_ = crate::leanh::lean_ctor_get(v___x_4485_, 0);
                crate::leanh::lean_inc_ref(v_env_4486_);
                crate::leanh::lean_dec(v___x_4485_);
                v___x_4487_ = 1;
                crate::leanh::lean_inc(v_a_4481_);
                v___x_4488_ = l_Lean_Environment_contains(v_env_4486_, v_a_4481_, v___x_4487_);
                if v___x_4488_ == 0 {
                    crate::leanh::lean_dec(v_stx_4476_);
                    if v_isShared_4484_ == 0 {
                        v___x_4490_ = v___x_4483_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4481_);
                        v___x_4490_ = v_reuseFailAlloc_4491_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4483_);
                    v___x_4492_ = 0;
                    crate::leanh::lean_inc(v_a_4481_);
                    v___x_4493_ =
                        l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(
                            v_a_4481_,
                            v___x_4492_,
                            v___y_4477_,
                            v___y_4478_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4493_) == 0 {
                        v_isSharedCheck_4523_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4493_)) as u8;
                        if v_isSharedCheck_4523_ == 0 {
                            v_unused_4524_ = crate::leanh::lean_ctor_get(v___x_4493_, 0);
                            crate::leanh::lean_dec(v_unused_4524_);
                            v___x_4495_ = v___x_4493_;
                            v_isShared_4496_ = v_isSharedCheck_4523_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4493_);
                            v___x_4495_ = crate::leanh::lean_box(0);
                            v_isShared_4496_ = v_isSharedCheck_4523_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4481_);
                        crate::leanh::lean_dec(v_stx_4476_);
                        v_a_4525_ = crate::leanh::lean_ctor_get(v___x_4493_, 0);
                        v_isSharedCheck_4532_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4493_)) as u8;
                        if v_isSharedCheck_4532_ == 0 {
                            v___x_4527_ = v___x_4493_;
                            v_isShared_4528_ = v_isSharedCheck_4532_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4525_);
                            crate::leanh::lean_dec(v___x_4493_);
                            v___x_4527_ = crate::leanh::lean_box(0);
                            v_isShared_4528_ = v_isSharedCheck_4532_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4490_;
            }
            3 => {
                v___x_4497_ = lean_st_ref_get(v___y_4478_);
                v_infoState_4498_ = crate::leanh::lean_ctor_get(v___x_4497_, 7);
                crate::leanh::lean_inc_ref(v_infoState_4498_);
                crate::leanh::lean_dec(v___x_4497_);
                v_enabled_4499_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_4498_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_4498_);
                if v_enabled_4499_ == 0 {
                    crate::leanh::lean_dec(v_stx_4476_);
                    if v_isShared_4496_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4495_, 0, v_a_4481_);
                        v___x_4501_ = v___x_4495_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4481_);
                        v___x_4501_ = v_reuseFailAlloc_4502_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4495_);
                    v___x_4503_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4504_ = l_Lean_Syntax_getArg(v_stx_4476_, v___x_4503_);
                    crate::leanh::lean_dec(v_stx_4476_);
                    v___x_4505_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_4481_);
                    v___x_4506_ =
                        l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(
                            v___x_4504_,
                            v_a_4481_,
                            v___x_4505_,
                            v___y_4477_,
                            v___y_4478_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4506_) == 0 {
                        v_isSharedCheck_4513_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4506_)) as u8;
                        if v_isSharedCheck_4513_ == 0 {
                            v_unused_4514_ = crate::leanh::lean_ctor_get(v___x_4506_, 0);
                            crate::leanh::lean_dec(v_unused_4514_);
                            v___x_4508_ = v___x_4506_;
                            v_isShared_4509_ = v_isSharedCheck_4513_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4506_);
                            v___x_4508_ = crate::leanh::lean_box(0);
                            v_isShared_4509_ = v_isSharedCheck_4513_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4481_);
                        v_a_4515_ = crate::leanh::lean_ctor_get(v___x_4506_, 0);
                        v_isSharedCheck_4522_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4506_)) as u8;
                        if v_isSharedCheck_4522_ == 0 {
                            v___x_4517_ = v___x_4506_;
                            v_isShared_4518_ = v_isSharedCheck_4522_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4515_);
                            crate::leanh::lean_dec(v___x_4506_);
                            v___x_4517_ = crate::leanh::lean_box(0);
                            v_isShared_4518_ = v_isSharedCheck_4522_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_4501_;
            }
            5 => {
                if v_isShared_4509_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4508_, 0, v_a_4481_);
                    v___x_4511_ = v___x_4508_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4481_);
                    v___x_4511_ = v_reuseFailAlloc_4512_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4511_;
            }
            7 => {
                if v_isShared_4518_ == 0 {
                    v___x_4520_ = v___x_4517_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
                    v___x_4520_ = v_reuseFailAlloc_4521_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4520_;
            }
            9 => {
                if v_isShared_4528_ == 0 {
                    v___x_4530_ = v___x_4527_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4531_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4525_);
                    v___x_4530_ = v_reuseFailAlloc_4531_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed(
    mut v_parserNamespace_4534_: *mut crate::leanh::LeanObject,
    mut v_x_4535_: *mut crate::leanh::LeanObject,
    mut v_stx_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
    mut v___y_4538_: *mut crate::leanh::LeanObject,
    mut v___y_4539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7364__boxed_4540_: u8 = 0;
    let mut v_res_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7364__boxed_4540_ = (crate::leanh::lean_unbox(v_x_4535_) as u8);
    v_res_4541_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(
        v_parserNamespace_4534_,
        v_x_7364__boxed_4540_,
        v_stx_4536_,
        v___y_4537_,
        v___y_4538_,
    );
    crate::leanh::lean_dec(v___y_4538_);
    crate::leanh::lean_dec_ref(v___y_4537_);
    return v_res_4541_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg(
    mut v_attrBuiltinName_4544_: *mut crate::leanh::LeanObject,
    mut v_attrName_4545_: *mut crate::leanh::LeanObject,
    mut v_parserNamespace_4546_: *mut crate::leanh::LeanObject,
    mut v_typeName_4547_: *mut crate::leanh::LeanObject,
    mut v_kind_4548_: *mut crate::leanh::LeanObject,
    mut v_attrDeclName_4549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4551_ = l_Lean_Elab_mkElabAttribute___redArg___closed__0;
    v___f_4552_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4552_, 0, v_parserNamespace_4546_);
    v___x_4553_ = l_Lean_Elab_mkElabAttribute___redArg___closed__1;
    v___x_4554_ = lean_string_append(v_kind_4548_, v___x_4553_);
    v___x_4555_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4555_, 0, v_attrBuiltinName_4544_);
    crate::leanh::lean_ctor_set(v___x_4555_, 1, v_attrName_4545_);
    crate::leanh::lean_ctor_set(v___x_4555_, 2, v___x_4554_);
    crate::leanh::lean_ctor_set(v___x_4555_, 3, v_typeName_4547_);
    crate::leanh::lean_ctor_set(v___x_4555_, 4, v___f_4552_);
    crate::leanh::lean_ctor_set(v___x_4555_, 5, v___f_4551_);
    v___x_4556_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4555_, v_attrDeclName_4549_);
    return v___x_4556_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg___boxed(
    mut v_attrBuiltinName_4557_: *mut crate::leanh::LeanObject,
    mut v_attrName_4558_: *mut crate::leanh::LeanObject,
    mut v_parserNamespace_4559_: *mut crate::leanh::LeanObject,
    mut v_typeName_4560_: *mut crate::leanh::LeanObject,
    mut v_kind_4561_: *mut crate::leanh::LeanObject,
    mut v_attrDeclName_4562_: *mut crate::leanh::LeanObject,
    mut v_a_4563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4564_ = l_Lean_Elab_mkElabAttribute___redArg(
        v_attrBuiltinName_4557_,
        v_attrName_4558_,
        v_parserNamespace_4559_,
        v_typeName_4560_,
        v_kind_4561_,
        v_attrDeclName_4562_,
    );
    return v_res_4564_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute(
    mut v_00_u03b3_4565_: *mut crate::leanh::LeanObject,
    mut v_attrBuiltinName_4566_: *mut crate::leanh::LeanObject,
    mut v_attrName_4567_: *mut crate::leanh::LeanObject,
    mut v_parserNamespace_4568_: *mut crate::leanh::LeanObject,
    mut v_typeName_4569_: *mut crate::leanh::LeanObject,
    mut v_kind_4570_: *mut crate::leanh::LeanObject,
    mut v_attrDeclName_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4573_ = l_Lean_Elab_mkElabAttribute___redArg(
        v_attrBuiltinName_4566_,
        v_attrName_4567_,
        v_parserNamespace_4568_,
        v_typeName_4569_,
        v_kind_4570_,
        v_attrDeclName_4571_,
    );
    return v___x_4573_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___boxed(
    mut v_00_u03b3_4574_: *mut crate::leanh::LeanObject,
    mut v_attrBuiltinName_4575_: *mut crate::leanh::LeanObject,
    mut v_attrName_4576_: *mut crate::leanh::LeanObject,
    mut v_parserNamespace_4577_: *mut crate::leanh::LeanObject,
    mut v_typeName_4578_: *mut crate::leanh::LeanObject,
    mut v_kind_4579_: *mut crate::leanh::LeanObject,
    mut v_attrDeclName_4580_: *mut crate::leanh::LeanObject,
    mut v_a_4581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4582_ = l_Lean_Elab_mkElabAttribute(
        v_00_u03b3_4574_,
        v_attrBuiltinName_4575_,
        v_attrName_4576_,
        v_parserNamespace_4577_,
        v_typeName_4578_,
        v_kind_4579_,
        v_attrDeclName_4580_,
    );
    return v_res_4582_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(
    mut v_00_u03b2_4583_: *mut crate::leanh::LeanObject,
    mut v_m_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_4584_, v_a_4585_);
    return v___x_4586_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(
    mut v_00_u03b2_4587_: *mut crate::leanh::LeanObject,
    mut v_m_4588_: *mut crate::leanh::LeanObject,
    mut v_a_4589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_4587_, v_m_4588_, v_a_4589_);
    crate::leanh::lean_dec(v_a_4589_);
    crate::leanh::lean_dec_ref(v_m_4588_);
    return v_res_4590_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(
    mut v_t_4591_: *mut crate::leanh::LeanObject,
    mut v___y_4592_: *mut crate::leanh::LeanObject,
    mut v___y_4593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4595_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_4591_, v___y_4593_);
    return v___x_4595_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(
    mut v_t_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4600_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_4596_, v___y_4597_, v___y_4598_);
    crate::leanh::lean_dec(v___y_4598_);
    crate::leanh::lean_dec_ref(v___y_4597_);
    return v_res_4600_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4601_: *mut crate::leanh::LeanObject,
    mut v_x_4602_: *mut crate::leanh::LeanObject,
    mut v_x_4603_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4604_: u8 = 0;
    v___x_4604_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_4602_, v_x_4603_);
    return v___x_4604_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4605_: *mut crate::leanh::LeanObject,
    mut v_x_4606_: *mut crate::leanh::LeanObject,
    mut v_x_4607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4608_: u8 = 0;
    let mut v_r_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4608_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_4605_, v_x_4606_, v_x_4607_);
    crate::leanh::lean_dec_ref(v_x_4607_);
    crate::leanh::lean_dec_ref(v_x_4606_);
    v_r_4609_ = crate::leanh::lean_box((v_res_4608_) as usize);
    return v_r_4609_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(
    mut v_00_u03b2_4610_: *mut crate::leanh::LeanObject,
    mut v_a_4611_: *mut crate::leanh::LeanObject,
    mut v_x_4612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4613_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_4611_, v_x_4612_);
    return v___x_4613_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b2_4614_: *mut crate::leanh::LeanObject,
    mut v_a_4615_: *mut crate::leanh::LeanObject,
    mut v_x_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4617_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_4614_, v_a_4615_, v_x_4616_);
    crate::leanh::lean_dec(v_x_4616_);
    crate::leanh::lean_dec(v_a_4615_);
    return v_res_4617_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4618_: *mut crate::leanh::LeanObject,
    mut v_x_4619_: *mut crate::leanh::LeanObject,
    mut v_x_4620_: usize,
    mut v_x_4621_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4622_: u8 = 0;
    v___x_4622_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4619_, v_x_4620_, v_x_4621_);
    return v___x_4622_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4623_: *mut crate::leanh::LeanObject,
    mut v_x_4624_: *mut crate::leanh::LeanObject,
    mut v_x_4625_: *mut crate::leanh::LeanObject,
    mut v_x_4626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7534__boxed_4627_: usize = 0;
    let mut v_res_4628_: u8 = 0;
    let mut v_r_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7534__boxed_4627_ = crate::leanh::lean_unbox_usize(v_x_4625_);
    crate::leanh::lean_dec(v_x_4625_);
    v_res_4628_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4623_, v_x_4624_, v_x_7534__boxed_4627_, v_x_4626_);
    crate::leanh::lean_dec_ref(v_x_4626_);
    crate::leanh::lean_dec_ref(v_x_4624_);
    v_r_4629_ = crate::leanh::lean_box((v_res_4628_) as usize);
    return v_r_4629_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(
    mut v_00_u03b1_4630_: *mut crate::leanh::LeanObject,
    mut v_constName_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4635_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_4631_, v___y_4632_, v___y_4633_);
    return v___x_4635_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(
    mut v_00_u03b1_4636_: *mut crate::leanh::LeanObject,
    mut v_constName_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4641_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_4636_, v_constName_4637_, v___y_4638_, v___y_4639_);
    crate::leanh::lean_dec(v___y_4639_);
    crate::leanh::lean_dec_ref(v___y_4638_);
    return v_res_4641_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(
    mut v_00_u03b2_4642_: *mut crate::leanh::LeanObject,
    mut v_keys_4643_: *mut crate::leanh::LeanObject,
    mut v_vals_4644_: *mut crate::leanh::LeanObject,
    mut v_heq_4645_: *mut crate::leanh::LeanObject,
    mut v_i_4646_: *mut crate::leanh::LeanObject,
    mut v_k_4647_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4648_: u8 = 0;
    v___x_4648_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_4643_, v_i_4646_, v_k_4647_);
    return v___x_4648_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(
    mut v_00_u03b2_4649_: *mut crate::leanh::LeanObject,
    mut v_keys_4650_: *mut crate::leanh::LeanObject,
    mut v_vals_4651_: *mut crate::leanh::LeanObject,
    mut v_heq_4652_: *mut crate::leanh::LeanObject,
    mut v_i_4653_: *mut crate::leanh::LeanObject,
    mut v_k_4654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4655_: u8 = 0;
    let mut v_r_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4655_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_4649_, v_keys_4650_, v_vals_4651_, v_heq_4652_, v_i_4653_, v_k_4654_);
    crate::leanh::lean_dec_ref(v_k_4654_);
    crate::leanh::lean_dec_ref(v_vals_4651_);
    crate::leanh::lean_dec_ref(v_keys_4650_);
    v_r_4656_ = crate::leanh::lean_box((v_res_4655_) as usize);
    return v_r_4656_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(
    mut v_00_u03b1_4657_: *mut crate::leanh::LeanObject,
    mut v_ref_4658_: *mut crate::leanh::LeanObject,
    mut v_constName_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_4658_, v_constName_4659_, v___y_4660_, v___y_4661_);
    return v___x_4663_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(
    mut v_00_u03b1_4664_: *mut crate::leanh::LeanObject,
    mut v_ref_4665_: *mut crate::leanh::LeanObject,
    mut v_constName_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
    mut v___y_4668_: *mut crate::leanh::LeanObject,
    mut v___y_4669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4670_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_4664_, v_ref_4665_, v_constName_4666_, v___y_4667_, v___y_4668_);
    crate::leanh::lean_dec(v___y_4668_);
    crate::leanh::lean_dec_ref(v___y_4667_);
    crate::leanh::lean_dec(v_ref_4665_);
    return v_res_4670_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(
    mut v_00_u03b1_4671_: *mut crate::leanh::LeanObject,
    mut v_ref_4672_: *mut crate::leanh::LeanObject,
    mut v_msg_4673_: *mut crate::leanh::LeanObject,
    mut v_declHint_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
    mut v___y_4676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4678_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_4672_, v_msg_4673_, v_declHint_4674_, v___y_4675_, v___y_4676_);
    return v___x_4678_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(
    mut v_00_u03b1_4679_: *mut crate::leanh::LeanObject,
    mut v_ref_4680_: *mut crate::leanh::LeanObject,
    mut v_msg_4681_: *mut crate::leanh::LeanObject,
    mut v_declHint_4682_: *mut crate::leanh::LeanObject,
    mut v___y_4683_: *mut crate::leanh::LeanObject,
    mut v___y_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4686_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_4679_, v_ref_4680_, v_msg_4681_, v_declHint_4682_, v___y_4683_, v___y_4684_);
    crate::leanh::lean_dec(v___y_4684_);
    crate::leanh::lean_dec_ref(v___y_4683_);
    crate::leanh::lean_dec(v_ref_4680_);
    return v_res_4686_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(
    mut v_msg_4687_: *mut crate::leanh::LeanObject,
    mut v_declHint_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4692_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_4687_, v_declHint_4688_, v___y_4690_);
    return v___x_4692_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(
    mut v_msg_4693_: *mut crate::leanh::LeanObject,
    mut v_declHint_4694_: *mut crate::leanh::LeanObject,
    mut v___y_4695_: *mut crate::leanh::LeanObject,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_4693_, v_declHint_4694_, v___y_4695_, v___y_4696_);
    crate::leanh::lean_dec(v___y_4696_);
    crate::leanh::lean_dec_ref(v___y_4695_);
    return v_res_4698_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(
    mut v_00_u03b1_4699_: *mut crate::leanh::LeanObject,
    mut v_ref_4700_: *mut crate::leanh::LeanObject,
    mut v_msg_4701_: *mut crate::leanh::LeanObject,
    mut v___y_4702_: *mut crate::leanh::LeanObject,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4705_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_4700_, v_msg_4701_, v___y_4702_, v___y_4703_);
    return v___x_4705_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(
    mut v_00_u03b1_4706_: *mut crate::leanh::LeanObject,
    mut v_ref_4707_: *mut crate::leanh::LeanObject,
    mut v_msg_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4712_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_4706_, v_ref_4707_, v_msg_4708_, v___y_4709_, v___y_4710_);
    crate::leanh::lean_dec(v___y_4710_);
    crate::leanh::lean_dec_ref(v___y_4709_);
    crate::leanh::lean_dec(v_ref_4707_);
    return v_res_4712_;
}
pub unsafe fn l_Lean_Elab_mkMacroAttributeUnsafe(
    mut v_ref_4723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4725_ = l_Lean_Elab_mkMacroAttributeUnsafe___closed__1;
    v___x_4726_ = l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
    v___x_4727_ = l_Lean_Elab_mkMacroAttributeUnsafe___closed__3;
    v___x_4728_ = crate::leanh::lean_box(0);
    v___x_4729_ = l_Lean_Elab_mkMacroAttributeUnsafe___closed__5;
    v___x_4730_ = l_Lean_Elab_mkElabAttribute___redArg(
        v___x_4725_,
        v___x_4727_,
        v___x_4728_,
        v___x_4729_,
        v___x_4726_,
        v_ref_4723_,
    );
    return v___x_4730_;
}
pub unsafe fn l_Lean_Elab_mkMacroAttributeUnsafe___boxed(
    mut v_ref_4731_: *mut crate::leanh::LeanObject,
    mut v_a_4732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4733_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_4731_);
    return v_res_4733_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4740_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_;
    v___x_4741_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_4740_);
    return v___x_4741_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(
    mut v_a_4742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4743_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
    return v_res_4743_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4746_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_;
    v___x_4747_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0;
    v___x_4748_ = l_Lean_addBuiltinDocString(v___x_4746_, v___x_4747_);
    return v___x_4748_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(
    mut v_a_4749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4750_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
    return v_res_4750_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4777_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_;
    v___x_4778_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6;
    v___x_4779_ = l_Lean_addBuiltinDeclarationRanges(v___x_4777_, v___x_4778_);
    return v___x_4779_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(
    mut v_a_4780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4781_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
    return v_res_4781_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(
    mut v_toOLeanEntry_4782_: *mut crate::leanh::LeanObject,
    mut v_a_4783_: *mut crate::leanh::LeanObject,
    mut v_____r_4784_: *mut crate::leanh::LeanObject,
    mut v___y_4785_: *mut crate::leanh::LeanObject,
    mut v___y_4786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4790_: u8 = 0;
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4798_: u8 = 0;
    let mut v_unused_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_4787_ = crate::leanh::lean_ctor_get(v_toOLeanEntry_4782_, 1);
                v_isSharedCheck_4798_ =
                    (!crate::leanh::lean_is_exclusive(v_toOLeanEntry_4782_)) as u8;
                if v_isSharedCheck_4798_ == 0 {
                    v_unused_4799_ = crate::leanh::lean_ctor_get(v_toOLeanEntry_4782_, 0);
                    crate::leanh::lean_dec(v_unused_4799_);
                    v___x_4789_ = v_toOLeanEntry_4782_;
                    v_isShared_4790_ = v_isSharedCheck_4798_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_declName_4787_);
                    crate::leanh::lean_dec(v_toOLeanEntry_4782_);
                    v___x_4789_ = crate::leanh::lean_box(0);
                    v_isShared_4790_ = v_isSharedCheck_4798_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4791_, 0, v_a_4783_);
                if v_isShared_4790_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4789_, 1, v___x_4791_);
                    crate::leanh::lean_ctor_set(v___x_4789_, 0, v_declName_4787_);
                    v___x_4793_ = v___x_4789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4797_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_declName_4787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 1, v___x_4791_);
                    v___x_4793_ = v_reuseFailAlloc_4797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4794_, 0, v___x_4793_);
                v___x_4795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4795_, 0, v___x_4794_);
                v___x_4796_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4796_, 0, v___x_4795_);
                crate::leanh::lean_ctor_set(v___x_4796_, 1, v___y_4786_);
                return v___x_4796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(
    mut v_toOLeanEntry_4800_: *mut crate::leanh::LeanObject,
    mut v_a_4801_: *mut crate::leanh::LeanObject,
    mut v_____r_4802_: *mut crate::leanh::LeanObject,
    mut v___y_4803_: *mut crate::leanh::LeanObject,
    mut v___y_4804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4805_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(
            v_toOLeanEntry_4800_,
            v_a_4801_,
            v_____r_4802_,
            v___y_4803_,
            v___y_4804_,
        );
    crate::leanh::lean_dec_ref(v___y_4803_);
    return v_res_4805_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(
    mut v_stx_4809_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4810_: *mut crate::leanh::LeanObject,
    mut v_b_4811_: *mut crate::leanh::LeanObject,
    mut v___y_4812_: *mut crate::leanh::LeanObject,
    mut v___y_4813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toOLeanEntry_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isBuiltin_4818_: u8 = 0;
    let mut v_value_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v_methods_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v_macroScope_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4870_: u8 = 0;
    let mut v_declName_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_isSharedCheck_4880_: u8 = 0;
    let mut v_a_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4810_) == 0 {
                    crate::leanh::lean_dec(v_stx_4809_);
                    v___x_4814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4814_, 0, v_b_4811_);
                    crate::leanh::lean_ctor_set(v___x_4814_, 1, v___y_4813_);
                    return v___x_4814_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4811_);
                    v_head_4815_ = crate::leanh::lean_ctor_get(v_as_x27_4810_, 0);
                    v_tail_4816_ = crate::leanh::lean_ctor_get(v_as_x27_4810_, 1);
                    v_toOLeanEntry_4817_ = crate::leanh::lean_ctor_get(v_head_4815_, 0);
                    v_isBuiltin_4818_ = crate::leanh::lean_ctor_get_uint8(
                        v_head_4815_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v_value_4819_ = crate::leanh::lean_ctor_get(v_head_4815_, 1);
                    v_macroScope_4820_ = crate::leanh::lean_ctor_get(v___y_4813_, 0);
                    v_traceMsgs_4821_ = crate::leanh::lean_ctor_get(v___y_4813_, 1);
                    v_expandedMacroDecls_4822_ = crate::leanh::lean_ctor_get(v___y_4813_, 2);
                    v_isSharedCheck_4887_ = (!crate::leanh::lean_is_exclusive(v___y_4813_)) as u8;
                    if v_isSharedCheck_4887_ == 0 {
                        v___x_4824_ = v___y_4813_;
                        v_isShared_4825_ = v_isSharedCheck_4887_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_expandedMacroDecls_4822_);
                        crate::leanh::lean_inc(v_traceMsgs_4821_);
                        crate::leanh::lean_inc(v_macroScope_4820_);
                        crate::leanh::lean_dec(v___y_4813_);
                        v___x_4824_ = crate::leanh::lean_box(0);
                        v_isShared_4825_ = v_isSharedCheck_4887_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_methods_4826_ = crate::leanh::lean_ctor_get(v___y_4812_, 0);
                v_quotContext_4827_ = crate::leanh::lean_ctor_get(v___y_4812_, 1);
                v_currRecDepth_4828_ = crate::leanh::lean_ctor_get(v___y_4812_, 3);
                v_maxRecDepth_4829_ = crate::leanh::lean_ctor_get(v___y_4812_, 4);
                v_ref_4830_ = crate::leanh::lean_ctor_get(v___y_4812_, 5);
                v___x_4831_ = crate::leanh::lean_box(0);
                v___x_4838_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0;
                v___x_4854_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4855_ = lean_nat_add(v_macroScope_4820_, v___x_4854_);
                if v_isShared_4825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4824_, 0, v___x_4855_);
                    v___x_4857_ = v___x_4824_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 1, v_traceMsgs_4821_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4886_,
                        2,
                        v_expandedMacroDecls_4822_,
                    );
                    v___x_4857_ = v_reuseFailAlloc_4886_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                v___x_4835_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4835_, 0, v_a_4833_);
                v___x_4836_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4836_, 0, v___x_4835_);
                crate::leanh::lean_ctor_set(v___x_4836_, 1, v___x_4831_);
                v___x_4837_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4837_, 0, v___x_4836_);
                crate::leanh::lean_ctor_set(v___x_4837_, 1, v_a_4834_);
                return v___x_4837_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_4840_) == 1 {
                    v_as_x27_4810_ = v_tail_4816_;
                    v_b_4811_ = v___x_4838_;
                    v___y_4813_ = v_a_4841_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_stx_4809_);
                    v_declName_4843_ = crate::leanh::lean_ctor_get(v_toOLeanEntry_4817_, 1);
                    v___x_4844_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4844_, 0, v_a_4840_);
                    crate::leanh::lean_inc(v_declName_4843_);
                    v___x_4845_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4845_, 0, v_declName_4843_);
                    crate::leanh::lean_ctor_set(v___x_4845_, 1, v___x_4844_);
                    v___x_4846_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4846_, 0, v___x_4845_);
                    v_a_4833_ = v___x_4846_;
                    v_a_4834_ = v_a_4841_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_a_4849_ = crate::leanh::lean_ctor_get(v___y_4848_, 0);
                if crate::leanh::lean_obj_tag(v_a_4849_) == 0 {
                    crate::leanh::lean_inc_ref(v_a_4849_);
                    crate::leanh::lean_dec(v_stx_4809_);
                    v_a_4850_ = crate::leanh::lean_ctor_get(v___y_4848_, 1);
                    crate::leanh::lean_inc(v_a_4850_);
                    crate::leanh::lean_dec_ref(v___y_4848_);
                    v_a_4851_ = crate::leanh::lean_ctor_get(v_a_4849_, 0);
                    crate::leanh::lean_inc(v_a_4851_);
                    crate::leanh::lean_dec_ref_known(v_a_4849_, 1);
                    v_a_4833_ = v_a_4851_;
                    v_a_4834_ = v_a_4850_;
                    state = 2;
                    continue;
                } else {
                    v_a_4852_ = crate::leanh::lean_ctor_get(v___y_4848_, 1);
                    crate::leanh::lean_inc(v_a_4852_);
                    crate::leanh::lean_dec_ref(v___y_4848_);
                    v_as_x27_4810_ = v_tail_4816_;
                    v_b_4811_ = v___x_4838_;
                    v___y_4813_ = v_a_4852_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_ref_4830_);
                crate::leanh::lean_inc(v_maxRecDepth_4829_);
                crate::leanh::lean_inc(v_currRecDepth_4828_);
                crate::leanh::lean_inc(v_quotContext_4827_);
                crate::leanh::lean_inc(v_methods_4826_);
                v___x_4858_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4858_, 0, v_methods_4826_);
                crate::leanh::lean_ctor_set(v___x_4858_, 1, v_quotContext_4827_);
                crate::leanh::lean_ctor_set(v___x_4858_, 2, v_macroScope_4820_);
                crate::leanh::lean_ctor_set(v___x_4858_, 3, v_currRecDepth_4828_);
                crate::leanh::lean_ctor_set(v___x_4858_, 4, v_maxRecDepth_4829_);
                crate::leanh::lean_ctor_set(v___x_4858_, 5, v_ref_4830_);
                crate::leanh::lean_inc(v_value_4819_);
                crate::leanh::lean_inc(v_stx_4809_);
                v___x_4859_ = crate::leanh::lean_apply_3(
                    v_value_4819_,
                    v_stx_4809_,
                    v___x_4858_,
                    v___x_4857_,
                );
                if crate::leanh::lean_obj_tag(v___x_4859_) == 0 {
                    if v_isBuiltin_4818_ == 0 {
                        v_a_4860_ = crate::leanh::lean_ctor_get(v___x_4859_, 1);
                        v_a_4861_ = crate::leanh::lean_ctor_get(v___x_4859_, 0);
                        v_isSharedCheck_4880_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4859_)) as u8;
                        if v_isSharedCheck_4880_ == 0 {
                            v___x_4863_ = v___x_4859_;
                            v_isShared_4864_ = v_isSharedCheck_4880_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4860_);
                            crate::leanh::lean_inc(v_a_4861_);
                            crate::leanh::lean_dec(v___x_4859_);
                            v___x_4863_ = crate::leanh::lean_box(0);
                            v_isShared_4864_ = v_isSharedCheck_4880_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4881_ = crate::leanh::lean_ctor_get(v___x_4859_, 0);
                        crate::leanh::lean_inc(v_a_4881_);
                        v_a_4882_ = crate::leanh::lean_ctor_get(v___x_4859_, 1);
                        crate::leanh::lean_inc(v_a_4882_);
                        crate::leanh::lean_dec_ref_known(v___x_4859_, 2);
                        crate::leanh::lean_inc_ref(v_toOLeanEntry_4817_);
                        v___x_4883_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_4817_, v_a_4881_, v___x_4831_, v___y_4812_, v_a_4882_);
                        v___y_4848_ = v___x_4883_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4884_ = crate::leanh::lean_ctor_get(v___x_4859_, 0);
                    crate::leanh::lean_inc(v_a_4884_);
                    v_a_4885_ = crate::leanh::lean_ctor_get(v___x_4859_, 1);
                    crate::leanh::lean_inc(v_a_4885_);
                    crate::leanh::lean_dec_ref_known(v___x_4859_, 2);
                    v_a_4840_ = v_a_4884_;
                    v_a_4841_ = v_a_4885_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                v_macroScope_4865_ = crate::leanh::lean_ctor_get(v_a_4860_, 0);
                v_traceMsgs_4866_ = crate::leanh::lean_ctor_get(v_a_4860_, 1);
                v_expandedMacroDecls_4867_ = crate::leanh::lean_ctor_get(v_a_4860_, 2);
                v_isSharedCheck_4879_ = (!crate::leanh::lean_is_exclusive(v_a_4860_)) as u8;
                if v_isSharedCheck_4879_ == 0 {
                    v___x_4869_ = v_a_4860_;
                    v_isShared_4870_ = v_isSharedCheck_4879_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_expandedMacroDecls_4867_);
                    crate::leanh::lean_inc(v_traceMsgs_4866_);
                    crate::leanh::lean_inc(v_macroScope_4865_);
                    crate::leanh::lean_dec(v_a_4860_);
                    v___x_4869_ = crate::leanh::lean_box(0);
                    v_isShared_4870_ = v_isSharedCheck_4879_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_declName_4871_ = crate::leanh::lean_ctor_get(v_toOLeanEntry_4817_, 1);
                crate::leanh::lean_inc(v_declName_4871_);
                if v_isShared_4864_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4863_, 1);
                    crate::leanh::lean_ctor_set(v___x_4863_, 1, v_expandedMacroDecls_4867_);
                    crate::leanh::lean_ctor_set(v___x_4863_, 0, v_declName_4871_);
                    v___x_4873_ = v___x_4863_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_declName_4871_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4878_,
                        1,
                        v_expandedMacroDecls_4867_,
                    );
                    v___x_4873_ = v_reuseFailAlloc_4878_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4869_, 2, v___x_4873_);
                    v___x_4875_ = v___x_4869_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4877_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_macroScope_4865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4877_, 1, v_traceMsgs_4866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4877_, 2, v___x_4873_);
                    v___x_4875_ = v_reuseFailAlloc_4877_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc_ref(v_toOLeanEntry_4817_);
                v___x_4876_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_4817_, v_a_4861_, v___x_4831_, v___y_4812_, v___x_4875_);
                v___y_4848_ = v___x_4876_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___boxed(
    mut v_stx_4888_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4889_: *mut crate::leanh::LeanObject,
    mut v_b_4890_: *mut crate::leanh::LeanObject,
    mut v___y_4891_: *mut crate::leanh::LeanObject,
    mut v___y_4892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4893_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(
        v_stx_4888_,
        v_as_x27_4889_,
        v_b_4890_,
        v___y_4891_,
        v___y_4892_,
    );
    crate::leanh::lean_dec_ref(v___y_4891_);
    crate::leanh::lean_dec(v_as_x27_4889_);
    return v_res_4893_;
}
pub unsafe fn l_Lean_Elab_expandMacroImpl_x3f(
    mut v_env_4894_: *mut crate::leanh::LeanObject,
    mut v_stx_4895_: *mut crate::leanh::LeanObject,
    mut v_a_4896_: *mut crate::leanh::LeanObject,
    mut v_a_4897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4909_: u8 = 0;
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4913_: u8 = 0;
    let mut v_unused_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v_val_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_unused_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4898_ = l_Lean_Elab_macroAttribute;
                crate::leanh::lean_inc(v_stx_4895_);
                v___x_4899_ = l_Lean_Syntax_getKind(v_stx_4895_);
                v___x_4900_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(
                    v___x_4898_,
                    v_env_4894_,
                    v___x_4899_,
                );
                crate::leanh::lean_dec(v___x_4899_);
                v___x_4901_ = crate::leanh::lean_box(0);
                v___x_4902_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0;
                v___x_4903_ =
                    l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(
                        v_stx_4895_,
                        v___x_4900_,
                        v___x_4902_,
                        v_a_4896_,
                        v_a_4897_,
                    );
                crate::leanh::lean_dec(v___x_4900_);
                v_a_4904_ = crate::leanh::lean_ctor_get(v___x_4903_, 0);
                crate::leanh::lean_inc(v_a_4904_);
                v_fst_4905_ = crate::leanh::lean_ctor_get(v_a_4904_, 0);
                crate::leanh::lean_inc(v_fst_4905_);
                crate::leanh::lean_dec(v_a_4904_);
                if crate::leanh::lean_obj_tag(v_fst_4905_) == 0 {
                    v_a_4906_ = crate::leanh::lean_ctor_get(v___x_4903_, 1);
                    v_isSharedCheck_4913_ = (!crate::leanh::lean_is_exclusive(v___x_4903_)) as u8;
                    if v_isSharedCheck_4913_ == 0 {
                        v_unused_4914_ = crate::leanh::lean_ctor_get(v___x_4903_, 0);
                        crate::leanh::lean_dec(v_unused_4914_);
                        v___x_4908_ = v___x_4903_;
                        v_isShared_4909_ = v_isSharedCheck_4913_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4906_);
                        crate::leanh::lean_dec(v___x_4903_);
                        v___x_4908_ = crate::leanh::lean_box(0);
                        v_isShared_4909_ = v_isSharedCheck_4913_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4915_ = crate::leanh::lean_ctor_get(v___x_4903_, 1);
                    v_isSharedCheck_4923_ = (!crate::leanh::lean_is_exclusive(v___x_4903_)) as u8;
                    if v_isSharedCheck_4923_ == 0 {
                        v_unused_4924_ = crate::leanh::lean_ctor_get(v___x_4903_, 0);
                        crate::leanh::lean_dec(v_unused_4924_);
                        v___x_4917_ = v___x_4903_;
                        v_isShared_4918_ = v_isSharedCheck_4923_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4915_);
                        crate::leanh::lean_dec(v___x_4903_);
                        v___x_4917_ = crate::leanh::lean_box(0);
                        v_isShared_4918_ = v_isSharedCheck_4923_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4909_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4908_, 0, v___x_4901_);
                    v___x_4911_ = v___x_4908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4912_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_a_4906_);
                    v___x_4911_ = v_reuseFailAlloc_4912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4911_;
            }
            3 => {
                v_val_4919_ = crate::leanh::lean_ctor_get(v_fst_4905_, 0);
                crate::leanh::lean_inc(v_val_4919_);
                crate::leanh::lean_dec_ref_known(v_fst_4905_, 1);
                if v_isShared_4918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4917_, 0, v_val_4919_);
                    v___x_4921_ = v___x_4917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4922_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_val_4919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_a_4915_);
                    v___x_4921_ = v_reuseFailAlloc_4922_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_expandMacroImpl_x3f___boxed(
    mut v_env_4925_: *mut crate::leanh::LeanObject,
    mut v_stx_4926_: *mut crate::leanh::LeanObject,
    mut v_a_4927_: *mut crate::leanh::LeanObject,
    mut v_a_4928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4929_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_4925_, v_stx_4926_, v_a_4927_, v_a_4928_);
    crate::leanh::lean_dec_ref(v_a_4927_);
    return v_res_4929_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(
    mut v_stx_4930_: *mut crate::leanh::LeanObject,
    mut v_as_4931_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4932_: *mut crate::leanh::LeanObject,
    mut v_b_4933_: *mut crate::leanh::LeanObject,
    mut v_a_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4937_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(
        v_stx_4930_,
        v_as_x27_4932_,
        v_b_4933_,
        v___y_4935_,
        v___y_4936_,
    );
    return v___x_4937_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___boxed(
    mut v_stx_4938_: *mut crate::leanh::LeanObject,
    mut v_as_4939_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4940_: *mut crate::leanh::LeanObject,
    mut v_b_4941_: *mut crate::leanh::LeanObject,
    mut v_a_4942_: *mut crate::leanh::LeanObject,
    mut v___y_4943_: *mut crate::leanh::LeanObject,
    mut v___y_4944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4945_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(
        v_stx_4938_,
        v_as_4939_,
        v_as_x27_4940_,
        v_b_4941_,
        v_a_4942_,
        v___y_4943_,
        v___y_4944_,
    );
    crate::leanh::lean_dec_ref(v___y_4943_);
    crate::leanh::lean_dec(v_as_x27_4940_);
    crate::leanh::lean_dec(v_as_4939_);
    return v_res_4945_;
}
pub unsafe fn l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(
    mut v_setNextMacroScope_4946_: *mut crate::leanh::LeanObject,
    mut v_inst_4947_: *mut crate::leanh::LeanObject,
    mut v_s_4948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4949_ = crate::leanh::lean_apply_1(v_setNextMacroScope_4946_, v_s_4948_);
    v___x_4950_ = crate::leanh::lean_apply_2(v_inst_4947_, crate::leanh::lean_box(0), v___x_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(
    mut v_inst_4951_: *mut crate::leanh::LeanObject,
    mut v_inst_4952_: *mut crate::leanh::LeanObject,
    mut v_inst_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getNextMacroScope_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setNextMacroScope_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4958_: u8 = 0;
    let mut v___f_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_unused_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getNextMacroScope_4954_ = crate::leanh::lean_ctor_get(v_inst_4953_, 1);
                v_setNextMacroScope_4955_ = crate::leanh::lean_ctor_get(v_inst_4953_, 2);
                v_isSharedCheck_4964_ = (!crate::leanh::lean_is_exclusive(v_inst_4953_)) as u8;
                if v_isSharedCheck_4964_ == 0 {
                    v_unused_4965_ = crate::leanh::lean_ctor_get(v_inst_4953_, 0);
                    crate::leanh::lean_dec(v_unused_4965_);
                    v___x_4957_ = v_inst_4953_;
                    v_isShared_4958_ = v_isSharedCheck_4964_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_setNextMacroScope_4955_);
                    crate::leanh::lean_inc(v_getNextMacroScope_4954_);
                    crate::leanh::lean_dec(v_inst_4953_);
                    v___x_4957_ = crate::leanh::lean_box(0);
                    v_isShared_4958_ = v_isSharedCheck_4964_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_inst_4951_);
                v___f_4959_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4959_, 0, v_setNextMacroScope_4955_);
                crate::leanh::lean_closure_set(v___f_4959_, 1, v_inst_4951_);
                v___x_4960_ = crate::leanh::lean_apply_2(
                    v_inst_4951_,
                    crate::leanh::lean_box(0),
                    v_getNextMacroScope_4954_,
                );
                if v_isShared_4958_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4957_, 2, v___f_4959_);
                    crate::leanh::lean_ctor_set(v___x_4957_, 1, v___x_4960_);
                    crate::leanh::lean_ctor_set(v___x_4957_, 0, v_inst_4952_);
                    v___x_4962_ = v___x_4957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4963_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_inst_4952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 1, v___x_4960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 2, v___f_4959_);
                    v___x_4962_ = v_reuseFailAlloc_4963_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation(
    mut v_m_4966_: *mut crate::leanh::LeanObject,
    mut v_n_4967_: *mut crate::leanh::LeanObject,
    mut v_inst_4968_: *mut crate::leanh::LeanObject,
    mut v_inst_4969_: *mut crate::leanh::LeanObject,
    mut v_inst_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getNextMacroScope_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setNextMacroScope_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4975_: u8 = 0;
    let mut v___f_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4981_: u8 = 0;
    let mut v_unused_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getNextMacroScope_4971_ = crate::leanh::lean_ctor_get(v_inst_4970_, 1);
                v_setNextMacroScope_4972_ = crate::leanh::lean_ctor_get(v_inst_4970_, 2);
                v_isSharedCheck_4981_ = (!crate::leanh::lean_is_exclusive(v_inst_4970_)) as u8;
                if v_isSharedCheck_4981_ == 0 {
                    v_unused_4982_ = crate::leanh::lean_ctor_get(v_inst_4970_, 0);
                    crate::leanh::lean_dec(v_unused_4982_);
                    v___x_4974_ = v_inst_4970_;
                    v_isShared_4975_ = v_isSharedCheck_4981_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_setNextMacroScope_4972_);
                    crate::leanh::lean_inc(v_getNextMacroScope_4971_);
                    crate::leanh::lean_dec(v_inst_4970_);
                    v___x_4974_ = crate::leanh::lean_box(0);
                    v_isShared_4975_ = v_isSharedCheck_4981_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_inst_4968_);
                v___f_4976_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4976_, 0, v_setNextMacroScope_4972_);
                crate::leanh::lean_closure_set(v___f_4976_, 1, v_inst_4968_);
                v___x_4977_ = crate::leanh::lean_apply_2(
                    v_inst_4968_,
                    crate::leanh::lean_box(0),
                    v_getNextMacroScope_4971_,
                );
                if v_isShared_4975_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4974_, 2, v___f_4976_);
                    crate::leanh::lean_ctor_set(v___x_4974_, 1, v___x_4977_);
                    crate::leanh::lean_ctor_set(v___x_4974_, 0, v_inst_4969_);
                    v___x_4979_ = v___x_4974_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4980_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_inst_4969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 1, v___x_4977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 2, v___f_4976_);
                    v___x_4979_ = v_reuseFailAlloc_4980_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__0(
    mut v_toPure_4983_: *mut crate::leanh::LeanObject,
    mut v_snd_4984_: *mut crate::leanh::LeanObject,
    mut v_inst_4985_: *mut crate::leanh::LeanObject,
    mut v_inst_4986_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_4987_: *mut crate::leanh::LeanObject,
    mut v_inst_4988_: *mut crate::leanh::LeanObject,
    mut v_fst_4989_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4990_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_4990_ == 0 {
        let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fst_4989_);
        crate::leanh::lean_dec(v_inst_4988_);
        crate::leanh::lean_dec_ref(v_toMonadRef_4987_);
        crate::leanh::lean_dec_ref(v_inst_4986_);
        crate::leanh::lean_dec_ref(v_inst_4985_);
        crate::leanh::lean_dec_ref(v_snd_4984_);
        v___x_4991_ = crate::leanh::lean_box(0);
        v___x_4992_ =
            crate::leanh::lean_apply_2(v_toPure_4983_, crate::leanh::lean_box(0), v___x_4991_);
        return v___x_4992_;
    } else {
        let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_4983_);
        v___x_4993_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4993_, 0, v_snd_4984_);
        v___x_4994_ = l_Lean_MessageData_ofFormat(v___x_4993_);
        v___x_4995_ = l_Lean_addTrace___redArg(
            v_inst_4985_,
            v_inst_4986_,
            v_toMonadRef_4987_,
            v_inst_4988_,
            v_fst_4989_,
            v___x_4994_,
        );
        return v___x_4995_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__0___boxed(
    mut v_toPure_4996_: *mut crate::leanh::LeanObject,
    mut v_snd_4997_: *mut crate::leanh::LeanObject,
    mut v_inst_4998_: *mut crate::leanh::LeanObject,
    mut v_inst_4999_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5000_: *mut crate::leanh::LeanObject,
    mut v_inst_5001_: *mut crate::leanh::LeanObject,
    mut v_fst_5002_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_1416__boxed_5004_: u8 = 0;
    let mut v_res_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_1416__boxed_5004_ = (crate::leanh::lean_unbox(v_____do__lift_5003_) as u8);
    v_res_5005_ = l_Lean_Elab_liftMacroM___redArg___lam__0(
        v_toPure_4996_,
        v_snd_4997_,
        v_inst_4998_,
        v_inst_4999_,
        v_toMonadRef_5000_,
        v_inst_5001_,
        v_fst_5002_,
        v_____do__lift_1416__boxed_5004_,
    );
    return v_res_5005_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__1(
    mut v_toPure_5006_: *mut crate::leanh::LeanObject,
    mut v_fst_5007_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5008_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasTrace_5010_: u8 = 0;
    v_hasTrace_5010_ = crate::leanh::lean_ctor_get_uint8(
        v_____do__lift_5009_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_5010_ == 0 {
        let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fst_5007_);
        v___x_5011_ = crate::leanh::lean_box((v_hasTrace_5010_) as usize);
        v___x_5012_ =
            crate::leanh::lean_apply_2(v_toPure_5006_, crate::leanh::lean_box(0), v___x_5011_);
        return v___x_5012_;
    } else {
        let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5015_: u8 = 0;
        let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5013_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14;
        v___x_5014_ = l_Lean_Name_append(v___x_5013_, v_fst_5007_);
        v___x_5015_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_5008_,
            v_____do__lift_5009_,
            v___x_5014_,
        );
        crate::leanh::lean_dec(v___x_5014_);
        v___x_5016_ = crate::leanh::lean_box((v___x_5015_) as usize);
        v___x_5017_ =
            crate::leanh::lean_apply_2(v_toPure_5006_, crate::leanh::lean_box(0), v___x_5016_);
        return v___x_5017_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__1___boxed(
    mut v_toPure_5018_: *mut crate::leanh::LeanObject,
    mut v_fst_5019_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5020_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5022_ = l_Lean_Elab_liftMacroM___redArg___lam__1(
        v_toPure_5018_,
        v_fst_5019_,
        v_____do__lift_5020_,
        v_____do__lift_5021_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_5021_);
    crate::leanh::lean_dec_ref(v_____do__lift_5020_);
    return v_res_5022_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__2(
    mut v_toPure_5023_: *mut crate::leanh::LeanObject,
    mut v_fst_5024_: *mut crate::leanh::LeanObject,
    mut v_toBind_5025_: *mut crate::leanh::LeanObject,
    mut v_inst_5026_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5028_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5028_, 0, v_toPure_5023_);
    crate::leanh::lean_closure_set(v___f_5028_, 1, v_fst_5024_);
    crate::leanh::lean_closure_set(v___f_5028_, 2, v_____do__lift_5027_);
    v___x_5029_ = crate::leanh::lean_apply_4(
        v_toBind_5025_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5026_,
        v___f_5028_,
    );
    return v___x_5029_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__3(
    mut v_inst_5030_: *mut crate::leanh::LeanObject,
    mut v_toPure_5031_: *mut crate::leanh::LeanObject,
    mut v_inst_5032_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5033_: *mut crate::leanh::LeanObject,
    mut v_inst_5034_: *mut crate::leanh::LeanObject,
    mut v_toBind_5035_: *mut crate::leanh::LeanObject,
    mut v_inst_5036_: *mut crate::leanh::LeanObject,
    mut v_x_5037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_5038_ = crate::leanh::lean_ctor_get(v_x_5037_, 0);
    crate::leanh::lean_inc_n(v_fst_5038_, 2);
    v_snd_5039_ = crate::leanh::lean_ctor_get(v_x_5037_, 1);
    crate::leanh::lean_inc(v_snd_5039_);
    crate::leanh::lean_dec_ref(v_x_5037_);
    v_getInheritedTraceOptions_5040_ = crate::leanh::lean_ctor_get(v_inst_5030_, 2);
    crate::leanh::lean_inc(v_getInheritedTraceOptions_5040_);
    crate::leanh::lean_inc(v_toPure_5031_);
    v___f_5041_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_5041_, 0, v_toPure_5031_);
    crate::leanh::lean_closure_set(v___f_5041_, 1, v_snd_5039_);
    crate::leanh::lean_closure_set(v___f_5041_, 2, v_inst_5032_);
    crate::leanh::lean_closure_set(v___f_5041_, 3, v_inst_5030_);
    crate::leanh::lean_closure_set(v___f_5041_, 4, v_toMonadRef_5033_);
    crate::leanh::lean_closure_set(v___f_5041_, 5, v_inst_5034_);
    crate::leanh::lean_closure_set(v___f_5041_, 6, v_fst_5038_);
    crate::leanh::lean_inc_n(v_toBind_5035_, 2);
    v___f_5042_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5042_, 0, v_toPure_5031_);
    crate::leanh::lean_closure_set(v___f_5042_, 1, v_fst_5038_);
    crate::leanh::lean_closure_set(v___f_5042_, 2, v_toBind_5035_);
    crate::leanh::lean_closure_set(v___f_5042_, 3, v_inst_5036_);
    v___x_5043_ = crate::leanh::lean_apply_4(
        v_toBind_5035_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getInheritedTraceOptions_5040_,
        v___f_5042_,
    );
    v___x_5044_ = crate::leanh::lean_apply_4(
        v_toBind_5035_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5043_,
        v___f_5041_,
    );
    return v___x_5044_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__4(
    mut v_env_5045_: *mut crate::leanh::LeanObject,
    mut v___x_5046_: *mut crate::leanh::LeanObject,
    mut v___x_5047_: *mut crate::leanh::LeanObject,
    mut v_stx_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5056_: u8 = 0;
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5061_: u8 = 0;
    let mut v_unused_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5066_: u8 = 0;
    let mut v_snd_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5072_: u8 = 0;
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195__overap_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5078_: u8 = 0;
    let mut v_a_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199__overap_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5092_: u8 = 0;
    let mut v_isSharedCheck_5093_: u8 = 0;
    let mut v_a_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5098_: u8 = 0;
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5051_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_5045_,
                    v_stx_5048_,
                    v___y_5049_,
                    v___y_5050_,
                );
                if crate::leanh::lean_obj_tag(v___x_5051_) == 0 {
                    v_a_5052_ = crate::leanh::lean_ctor_get(v___x_5051_, 0);
                    crate::leanh::lean_inc(v_a_5052_);
                    if crate::leanh::lean_obj_tag(v_a_5052_) == 0 {
                        crate::leanh::lean_dec(v___x_5047_);
                        crate::leanh::lean_dec_ref(v___x_5046_);
                        v_a_5053_ = crate::leanh::lean_ctor_get(v___x_5051_, 1);
                        v_isSharedCheck_5061_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5051_)) as u8;
                        if v_isSharedCheck_5061_ == 0 {
                            v_unused_5062_ = crate::leanh::lean_ctor_get(v___x_5051_, 0);
                            crate::leanh::lean_dec(v_unused_5062_);
                            v___x_5055_ = v___x_5051_;
                            v_isShared_5056_ = v_isSharedCheck_5061_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5053_);
                            crate::leanh::lean_dec(v___x_5051_);
                            v___x_5055_ = crate::leanh::lean_box(0);
                            v_isShared_5056_ = v_isSharedCheck_5061_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_5063_ = crate::leanh::lean_ctor_get(v_a_5052_, 0);
                        v_isSharedCheck_5093_ = (!crate::leanh::lean_is_exclusive(v_a_5052_)) as u8;
                        if v_isSharedCheck_5093_ == 0 {
                            v___x_5065_ = v_a_5052_;
                            v_isShared_5066_ = v_isSharedCheck_5093_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5063_);
                            crate::leanh::lean_dec(v_a_5052_);
                            v___x_5065_ = crate::leanh::lean_box(0);
                            v_isShared_5066_ = v_isSharedCheck_5093_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5047_);
                    crate::leanh::lean_dec_ref(v___x_5046_);
                    v_a_5094_ = crate::leanh::lean_ctor_get(v___x_5051_, 0);
                    v_a_5095_ = crate::leanh::lean_ctor_get(v___x_5051_, 1);
                    v_isSharedCheck_5102_ = (!crate::leanh::lean_is_exclusive(v___x_5051_)) as u8;
                    if v_isSharedCheck_5102_ == 0 {
                        v___x_5097_ = v___x_5051_;
                        v_isShared_5098_ = v_isSharedCheck_5102_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5095_);
                        crate::leanh::lean_inc(v_a_5094_);
                        crate::leanh::lean_dec(v___x_5051_);
                        v___x_5097_ = crate::leanh::lean_box(0);
                        v_isShared_5098_ = v_isSharedCheck_5102_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5057_ = crate::leanh::lean_box(0);
                if v_isShared_5056_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5055_, 0, v___x_5057_);
                    v___x_5059_ = v___x_5055_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5060_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_a_5053_);
                    v___x_5059_ = v_reuseFailAlloc_5060_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5059_;
            }
            3 => {
                v_snd_5067_ = crate::leanh::lean_ctor_get(v_val_5063_, 1);
                crate::leanh::lean_inc(v_snd_5067_);
                crate::leanh::lean_dec(v_val_5063_);
                if crate::leanh::lean_obj_tag(v_snd_5067_) == 0 {
                    crate::leanh::lean_del_object(v___x_5065_);
                    v_a_5068_ = crate::leanh::lean_ctor_get(v___x_5051_, 1);
                    crate::leanh::lean_inc(v_a_5068_);
                    crate::leanh::lean_dec_ref_known(v___x_5051_, 2);
                    v_a_5069_ = crate::leanh::lean_ctor_get(v_snd_5067_, 0);
                    v_isSharedCheck_5078_ = (!crate::leanh::lean_is_exclusive(v_snd_5067_)) as u8;
                    if v_isSharedCheck_5078_ == 0 {
                        v___x_5071_ = v_snd_5067_;
                        v_isShared_5072_ = v_isSharedCheck_5078_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5069_);
                        crate::leanh::lean_dec(v_snd_5067_);
                        v___x_5071_ = crate::leanh::lean_box(0);
                        v_isShared_5072_ = v_isSharedCheck_5078_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_5079_ = crate::leanh::lean_ctor_get(v___x_5051_, 1);
                    crate::leanh::lean_inc(v_a_5079_);
                    crate::leanh::lean_dec_ref_known(v___x_5051_, 2);
                    v_a_5080_ = crate::leanh::lean_ctor_get(v_snd_5067_, 0);
                    v_isSharedCheck_5092_ = (!crate::leanh::lean_is_exclusive(v_snd_5067_)) as u8;
                    if v_isSharedCheck_5092_ == 0 {
                        v___x_5082_ = v_snd_5067_;
                        v_isShared_5083_ = v_isSharedCheck_5092_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5080_);
                        crate::leanh::lean_dec(v_snd_5067_);
                        v___x_5082_ = crate::leanh::lean_box(0);
                        v_isShared_5083_ = v_isSharedCheck_5092_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5072_ == 0 {
                    v___x_5074_ = v___x_5071_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5069_);
                    v___x_5074_ = v_reuseFailAlloc_5077_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1195__overap_5075_ =
                    l_liftExcept___redArg(v___x_5046_, v___x_5047_, v___x_5074_);
                crate::leanh::lean_inc_ref(v___y_5049_);
                v___x_5076_ =
                    crate::leanh::lean_apply_2(v___x_1195__overap_5075_, v___y_5049_, v_a_5068_);
                return v___x_5076_;
            }
            6 => {
                if v_isShared_5066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5065_, 0, v_a_5080_);
                    v___x_5085_ = v___x_5065_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5080_);
                    v___x_5085_ = v_reuseFailAlloc_5091_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5082_, 0, v___x_5085_);
                    v___x_5087_ = v___x_5082_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5085_);
                    v___x_5087_ = v_reuseFailAlloc_5090_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1199__overap_5088_ =
                    l_liftExcept___redArg(v___x_5046_, v___x_5047_, v___x_5087_);
                crate::leanh::lean_inc_ref(v___y_5049_);
                v___x_5089_ =
                    crate::leanh::lean_apply_2(v___x_1199__overap_5088_, v___y_5049_, v_a_5079_);
                return v___x_5089_;
            }
            9 => {
                if v_isShared_5098_ == 0 {
                    v___x_5100_ = v___x_5097_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5101_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5101_, 1, v_a_5095_);
                    v___x_5100_ = v_reuseFailAlloc_5101_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__4___boxed(
    mut v_env_5103_: *mut crate::leanh::LeanObject,
    mut v___x_5104_: *mut crate::leanh::LeanObject,
    mut v___x_5105_: *mut crate::leanh::LeanObject,
    mut v_stx_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5109_ = l_Lean_Elab_liftMacroM___redArg___lam__4(
        v_env_5103_,
        v___x_5104_,
        v___x_5105_,
        v_stx_5106_,
        v___y_5107_,
        v___y_5108_,
    );
    crate::leanh::lean_dec_ref(v___y_5107_);
    return v_res_5109_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__5(
    mut v_env_5110_: *mut crate::leanh::LeanObject,
    mut v_declName_5111_: *mut crate::leanh::LeanObject,
    mut v___y_5112_: *mut crate::leanh::LeanObject,
    mut v___y_5113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5114_: u8 = 0;
    let mut v_env_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: u8 = 0;
    let mut v___x_5118_: u8 = 0;
    v___x_5114_ = 0;
    v_env_5115_ = l_Lean_Environment_setExporting(v_env_5110_, v___x_5114_);
    crate::leanh::lean_inc(v_declName_5111_);
    v___x_5116_ = l_Lean_mkPrivateName(v_env_5115_, v_declName_5111_);
    v___x_5117_ = 1;
    crate::leanh::lean_inc_ref(v_env_5115_);
    v___x_5118_ = l_Lean_Environment_contains(v_env_5115_, v___x_5116_, v___x_5117_);
    if v___x_5118_ == 0 {
        let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5120_: u8 = 0;
        let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5119_ = l_Lean_privateToUserName(v_declName_5111_);
        v___x_5120_ = l_Lean_Environment_contains(v_env_5115_, v___x_5119_, v___x_5117_);
        v___x_5121_ = crate::leanh::lean_box((v___x_5120_) as usize);
        v___x_5122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5122_, 0, v___x_5121_);
        crate::leanh::lean_ctor_set(v___x_5122_, 1, v___y_5113_);
        return v___x_5122_;
    } else {
        let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_5115_);
        crate::leanh::lean_dec(v_declName_5111_);
        v___x_5123_ = crate::leanh::lean_box((v___x_5118_) as usize);
        v___x_5124_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5124_, 0, v___x_5123_);
        crate::leanh::lean_ctor_set(v___x_5124_, 1, v___y_5113_);
        return v___x_5124_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(
    mut v_env_5125_: *mut crate::leanh::LeanObject,
    mut v_declName_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5129_ = l_Lean_Elab_liftMacroM___redArg___lam__5(
        v_env_5125_,
        v_declName_5126_,
        v___y_5127_,
        v___y_5128_,
    );
    crate::leanh::lean_dec_ref(v___y_5127_);
    return v_res_5129_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__6(
    mut v_env_5130_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5131_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5132_: *mut crate::leanh::LeanObject,
    mut v_n_5133_: *mut crate::leanh::LeanObject,
    mut v___y_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5136_ = l_Lean_ResolveName_resolveNamespace(
        v_env_5130_,
        v_currNamespace_5131_,
        v_openDecls_5132_,
        v_n_5133_,
    );
    v___x_5137_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5137_, 0, v___x_5136_);
    crate::leanh::lean_ctor_set(v___x_5137_, 1, v___y_5135_);
    return v___x_5137_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(
    mut v_env_5138_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5139_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5140_: *mut crate::leanh::LeanObject,
    mut v_n_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5144_ = l_Lean_Elab_liftMacroM___redArg___lam__6(
        v_env_5138_,
        v_currNamespace_5139_,
        v_openDecls_5140_,
        v_n_5141_,
        v___y_5142_,
        v___y_5143_,
    );
    crate::leanh::lean_dec_ref(v___y_5142_);
    return v_res_5144_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__7(
    mut v_env_5145_: *mut crate::leanh::LeanObject,
    mut v_opts_5146_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5147_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5148_: *mut crate::leanh::LeanObject,
    mut v_n_5149_: *mut crate::leanh::LeanObject,
    mut v___y_5150_: *mut crate::leanh::LeanObject,
    mut v___y_5151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5152_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_5145_,
        v_opts_5146_,
        v_currNamespace_5147_,
        v_openDecls_5148_,
        v_n_5149_,
    );
    v___x_5153_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5153_, 0, v___x_5152_);
    crate::leanh::lean_ctor_set(v___x_5153_, 1, v___y_5151_);
    return v___x_5153_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(
    mut v_env_5154_: *mut crate::leanh::LeanObject,
    mut v_opts_5155_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5156_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5157_: *mut crate::leanh::LeanObject,
    mut v_n_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
    mut v___y_5160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5161_ = l_Lean_Elab_liftMacroM___redArg___lam__7(
        v_env_5154_,
        v_opts_5155_,
        v_currNamespace_5156_,
        v_openDecls_5157_,
        v_n_5158_,
        v___y_5159_,
        v___y_5160_,
    );
    crate::leanh::lean_dec_ref(v___y_5159_);
    crate::leanh::lean_dec_ref(v_opts_5155_);
    return v_res_5161_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__8(
    mut v_toPure_5162_: *mut crate::leanh::LeanObject,
    mut v_a_5163_: *mut crate::leanh::LeanObject,
    mut v_____r_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5165_ = crate::leanh::lean_apply_2(v_toPure_5162_, crate::leanh::lean_box(0), v_a_5163_);
    return v___x_5165_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__9(
    mut v_traceMsgs_5166_: *mut crate::leanh::LeanObject,
    mut v_inst_5167_: *mut crate::leanh::LeanObject,
    mut v___f_5168_: *mut crate::leanh::LeanObject,
    mut v_toBind_5169_: *mut crate::leanh::LeanObject,
    mut v___f_5170_: *mut crate::leanh::LeanObject,
    mut v_____r_5171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5172_ = l_List_reverse___redArg(v_traceMsgs_5166_);
    v___x_5173_ = l_List_forM___redArg(v_inst_5167_, v___x_5172_, v___f_5168_);
    v___x_5174_ = crate::leanh::lean_apply_4(
        v_toBind_5169_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5173_,
        v___f_5170_,
    );
    return v___x_5174_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__10(
    mut v_setNextMacroScope_5175_: *mut crate::leanh::LeanObject,
    mut v_macroScope_5176_: *mut crate::leanh::LeanObject,
    mut v_toBind_5177_: *mut crate::leanh::LeanObject,
    mut v___f_5178_: *mut crate::leanh::LeanObject,
    mut v_____s_5179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5180_ = crate::leanh::lean_apply_1(v_setNextMacroScope_5175_, v_macroScope_5176_);
    v___x_5181_ = crate::leanh::lean_apply_4(
        v_toBind_5177_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5180_,
        v___f_5178_,
    );
    return v___x_5181_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__11(
    mut v___x_5182_: *mut crate::leanh::LeanObject,
    mut v_toPure_5183_: *mut crate::leanh::LeanObject,
    mut v_____r_5184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5185_, 0, v___x_5182_);
    v___x_5186_ =
        crate::leanh::lean_apply_2(v_toPure_5183_, crate::leanh::lean_box(0), v___x_5185_);
    return v___x_5186_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__12(
    mut v_inst_5187_: *mut crate::leanh::LeanObject,
    mut v_inst_5188_: *mut crate::leanh::LeanObject,
    mut v_inst_5189_: *mut crate::leanh::LeanObject,
    mut v_inst_5190_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5191_: *mut crate::leanh::LeanObject,
    mut v_inst_5192_: *mut crate::leanh::LeanObject,
    mut v_toBind_5193_: *mut crate::leanh::LeanObject,
    mut v___f_5194_: *mut crate::leanh::LeanObject,
    mut v_a_5195_: *mut crate::leanh::LeanObject,
    mut v_x_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5198_: u8 = 0;
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5198_ = 1;
    v___x_5199_ = l_Lean_recordExtraModUseFromDecl___redArg(
        v_inst_5187_,
        v_inst_5188_,
        v_inst_5189_,
        v_inst_5190_,
        v_toMonadRef_5191_,
        v_inst_5192_,
        v_a_5195_,
        v___x_5198_,
    );
    v___x_5200_ = crate::leanh::lean_apply_4(
        v_toBind_5193_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5199_,
        v___f_5194_,
    );
    return v___x_5200_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__13(
    mut v_methods_5202_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5203_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5204_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5205_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5206_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5207_: *mut crate::leanh::LeanObject,
    mut v_x_5208_: *mut crate::leanh::LeanObject,
    mut v_toPure_5209_: *mut crate::leanh::LeanObject,
    mut v_inst_5210_: *mut crate::leanh::LeanObject,
    mut v___f_5211_: *mut crate::leanh::LeanObject,
    mut v_toBind_5212_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5213_: *mut crate::leanh::LeanObject,
    mut v_inst_5214_: *mut crate::leanh::LeanObject,
    mut v_inst_5215_: *mut crate::leanh::LeanObject,
    mut v_inst_5216_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5217_: *mut crate::leanh::LeanObject,
    mut v_inst_5218_: *mut crate::leanh::LeanObject,
    mut v_inst_5219_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5220_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5222_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5222_, 0, v_methods_5202_);
    crate::leanh::lean_ctor_set(v___x_5222_, 1, v_____do__lift_5203_);
    crate::leanh::lean_ctor_set(v___x_5222_, 2, v_____do__lift_5204_);
    crate::leanh::lean_ctor_set(v___x_5222_, 3, v_____do__lift_5205_);
    crate::leanh::lean_ctor_set(v___x_5222_, 4, v_____do__lift_5206_);
    crate::leanh::lean_ctor_set(v___x_5222_, 5, v_____do__lift_5207_);
    v___x_5223_ = crate::leanh::lean_box(0);
    v___x_5224_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5224_, 0, v_____do__lift_5221_);
    crate::leanh::lean_ctor_set(v___x_5224_, 1, v___x_5223_);
    crate::leanh::lean_ctor_set(v___x_5224_, 2, v___x_5223_);
    v___x_5225_ = crate::leanh::lean_apply_2(v_x_5208_, v___x_5222_, v___x_5224_);
    if crate::leanh::lean_obj_tag(v___x_5225_) == 0 {
        let mut v_a_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_macroScope_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_traceMsgs_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expandedMacroDecls_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toMonadExceptOf_5220_);
        crate::leanh::lean_dec_ref(v_inst_5219_);
        v_a_5226_ = crate::leanh::lean_ctor_get(v___x_5225_, 1);
        crate::leanh::lean_inc(v_a_5226_);
        v_a_5227_ = crate::leanh::lean_ctor_get(v___x_5225_, 0);
        crate::leanh::lean_inc(v_a_5227_);
        crate::leanh::lean_dec_ref_known(v___x_5225_, 2);
        v_macroScope_5228_ = crate::leanh::lean_ctor_get(v_a_5226_, 0);
        crate::leanh::lean_inc(v_macroScope_5228_);
        v_traceMsgs_5229_ = crate::leanh::lean_ctor_get(v_a_5226_, 1);
        crate::leanh::lean_inc(v_traceMsgs_5229_);
        v_expandedMacroDecls_5230_ = crate::leanh::lean_ctor_get(v_a_5226_, 2);
        crate::leanh::lean_inc(v_expandedMacroDecls_5230_);
        crate::leanh::lean_dec(v_a_5226_);
        crate::leanh::lean_inc(v_toPure_5209_);
        v___f_5231_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__8 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5231_, 0, v_toPure_5209_);
        crate::leanh::lean_closure_set(v___f_5231_, 1, v_a_5227_);
        crate::leanh::lean_inc_n(v_toBind_5212_, 3);
        crate::leanh::lean_inc_ref_n(v_inst_5210_, 2);
        v___f_5232_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__9 as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_5232_, 0, v_traceMsgs_5229_);
        crate::leanh::lean_closure_set(v___f_5232_, 1, v_inst_5210_);
        crate::leanh::lean_closure_set(v___f_5232_, 2, v___f_5211_);
        crate::leanh::lean_closure_set(v___f_5232_, 3, v_toBind_5212_);
        crate::leanh::lean_closure_set(v___f_5232_, 4, v___f_5231_);
        v___f_5233_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__10 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5233_, 0, v_setNextMacroScope_5213_);
        crate::leanh::lean_closure_set(v___f_5233_, 1, v_macroScope_5228_);
        crate::leanh::lean_closure_set(v___f_5233_, 2, v_toBind_5212_);
        crate::leanh::lean_closure_set(v___f_5233_, 3, v___f_5232_);
        v___x_5234_ = crate::leanh::lean_box(0);
        v___f_5235_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__11 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5235_, 0, v___x_5234_);
        crate::leanh::lean_closure_set(v___f_5235_, 1, v_toPure_5209_);
        v___f_5236_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__12 as *mut core::ffi::c_void,
            11,
            8,
        );
        crate::leanh::lean_closure_set(v___f_5236_, 0, v_inst_5210_);
        crate::leanh::lean_closure_set(v___f_5236_, 1, v_inst_5214_);
        crate::leanh::lean_closure_set(v___f_5236_, 2, v_inst_5215_);
        crate::leanh::lean_closure_set(v___f_5236_, 3, v_inst_5216_);
        crate::leanh::lean_closure_set(v___f_5236_, 4, v_toMonadRef_5217_);
        crate::leanh::lean_closure_set(v___f_5236_, 5, v_inst_5218_);
        crate::leanh::lean_closure_set(v___f_5236_, 6, v_toBind_5212_);
        crate::leanh::lean_closure_set(v___f_5236_, 7, v___f_5235_);
        v___x_5237_ = l_List_forIn_x27_loop___redArg(
            v_inst_5210_,
            v___f_5236_,
            v_expandedMacroDecls_5230_,
            v___x_5234_,
        );
        crate::leanh::lean_dec(v_expandedMacroDecls_5230_);
        v___x_5238_ = crate::leanh::lean_apply_4(
            v_toBind_5212_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5237_,
            v___f_5233_,
        );
        return v___x_5238_;
    } else {
        let mut v_a_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_5218_);
        crate::leanh::lean_dec_ref(v_toMonadRef_5217_);
        crate::leanh::lean_dec(v_inst_5216_);
        crate::leanh::lean_dec_ref(v_inst_5215_);
        crate::leanh::lean_dec_ref(v_inst_5214_);
        crate::leanh::lean_dec(v_setNextMacroScope_5213_);
        crate::leanh::lean_dec(v_toBind_5212_);
        crate::leanh::lean_dec(v___f_5211_);
        crate::leanh::lean_dec(v_toPure_5209_);
        v_a_5239_ = crate::leanh::lean_ctor_get(v___x_5225_, 0);
        crate::leanh::lean_inc(v_a_5239_);
        crate::leanh::lean_dec_ref_known(v___x_5225_, 2);
        if crate::leanh::lean_obj_tag(v_a_5239_) == 0 {
            let mut v_a_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5243_: u8 = 0;
            crate::leanh::lean_dec_ref(v_toMonadExceptOf_5220_);
            v_a_5240_ = crate::leanh::lean_ctor_get(v_a_5239_, 0);
            crate::leanh::lean_inc(v_a_5240_);
            v_a_5241_ = crate::leanh::lean_ctor_get(v_a_5239_, 1);
            crate::leanh::lean_inc_ref(v_a_5241_);
            crate::leanh::lean_dec_ref_known(v_a_5239_, 2);
            v___x_5242_ = l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0;
            v___x_5243_ = lean_string_dec_eq(v_a_5241_, v___x_5242_);
            if v___x_5243_ == 0 {
                let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5244_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5244_, 0, v_a_5241_);
                v___x_5245_ = l_Lean_MessageData_ofFormat(v___x_5244_);
                v___x_5246_ = l_Lean_throwErrorAt___redArg(
                    v_inst_5210_,
                    v_inst_5219_,
                    v_a_5240_,
                    v___x_5245_,
                );
                return v___x_5246_;
            } else {
                let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_a_5241_);
                crate::leanh::lean_dec_ref(v_inst_5210_);
                v___x_5247_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_5219_, v_a_5240_);
                return v___x_5247_;
            }
        } else {
            let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_5219_);
            crate::leanh::lean_dec_ref(v_inst_5210_);
            v___x_5248_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_5220_);
            return v___x_5248_;
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_methods_5249_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_____do__lift_5250_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_____do__lift_5251_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_____do__lift_5252_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_____do__lift_5253_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_____do__lift_5254_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_x_5255_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_toPure_5256_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_5257_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_5258_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_toBind_5259_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_setNextMacroScope_5260_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_5261_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_5262_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_5263_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_toMonadRef_5264_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_5265_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_inst_5266_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_toMonadExceptOf_5267_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_____do__lift_5268_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5269_ = l_Lean_Elab_liftMacroM___redArg___lam__13(
        v_methods_5249_,
        v_____do__lift_5250_,
        v_____do__lift_5251_,
        v_____do__lift_5252_,
        v_____do__lift_5253_,
        v_____do__lift_5254_,
        v_x_5255_,
        v_toPure_5256_,
        v_inst_5257_,
        v___f_5258_,
        v_toBind_5259_,
        v_setNextMacroScope_5260_,
        v_inst_5261_,
        v_inst_5262_,
        v_inst_5263_,
        v_toMonadRef_5264_,
        v_inst_5265_,
        v_inst_5266_,
        v_toMonadExceptOf_5267_,
        v_____do__lift_5268_,
    );
    return v_res_5269_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__14(
    mut v_methods_5270_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5271_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5272_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5273_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5274_: *mut crate::leanh::LeanObject,
    mut v_x_5275_: *mut crate::leanh::LeanObject,
    mut v_toPure_5276_: *mut crate::leanh::LeanObject,
    mut v_inst_5277_: *mut crate::leanh::LeanObject,
    mut v___f_5278_: *mut crate::leanh::LeanObject,
    mut v_toBind_5279_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5280_: *mut crate::leanh::LeanObject,
    mut v_inst_5281_: *mut crate::leanh::LeanObject,
    mut v_inst_5282_: *mut crate::leanh::LeanObject,
    mut v_inst_5283_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5284_: *mut crate::leanh::LeanObject,
    mut v_inst_5285_: *mut crate::leanh::LeanObject,
    mut v_inst_5286_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5287_: *mut crate::leanh::LeanObject,
    mut v_getNextMacroScope_5288_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_5279_);
    v___f_5290_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__13___boxed as *mut core::ffi::c_void,
        20,
        19,
    );
    crate::leanh::lean_closure_set(v___f_5290_, 0, v_methods_5270_);
    crate::leanh::lean_closure_set(v___f_5290_, 1, v_____do__lift_5271_);
    crate::leanh::lean_closure_set(v___f_5290_, 2, v_____do__lift_5272_);
    crate::leanh::lean_closure_set(v___f_5290_, 3, v_____do__lift_5273_);
    crate::leanh::lean_closure_set(v___f_5290_, 4, v_____do__lift_5289_);
    crate::leanh::lean_closure_set(v___f_5290_, 5, v_____do__lift_5274_);
    crate::leanh::lean_closure_set(v___f_5290_, 6, v_x_5275_);
    crate::leanh::lean_closure_set(v___f_5290_, 7, v_toPure_5276_);
    crate::leanh::lean_closure_set(v___f_5290_, 8, v_inst_5277_);
    crate::leanh::lean_closure_set(v___f_5290_, 9, v___f_5278_);
    crate::leanh::lean_closure_set(v___f_5290_, 10, v_toBind_5279_);
    crate::leanh::lean_closure_set(v___f_5290_, 11, v_setNextMacroScope_5280_);
    crate::leanh::lean_closure_set(v___f_5290_, 12, v_inst_5281_);
    crate::leanh::lean_closure_set(v___f_5290_, 13, v_inst_5282_);
    crate::leanh::lean_closure_set(v___f_5290_, 14, v_inst_5283_);
    crate::leanh::lean_closure_set(v___f_5290_, 15, v_toMonadRef_5284_);
    crate::leanh::lean_closure_set(v___f_5290_, 16, v_inst_5285_);
    crate::leanh::lean_closure_set(v___f_5290_, 17, v_inst_5286_);
    crate::leanh::lean_closure_set(v___f_5290_, 18, v_toMonadExceptOf_5287_);
    v___x_5291_ = crate::leanh::lean_apply_4(
        v_toBind_5279_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getNextMacroScope_5288_,
        v___f_5290_,
    );
    return v___x_5291_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_methods_5292_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_____do__lift_5293_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_____do__lift_5294_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_____do__lift_5295_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_____do__lift_5296_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_x_5297_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_toPure_5298_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_inst_5299_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___f_5300_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_toBind_5301_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_setNextMacroScope_5302_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_5303_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_5304_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_5305_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_toMonadRef_5306_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_5307_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_5308_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_toMonadExceptOf_5309_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_getNextMacroScope_5310_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_____do__lift_5311_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5312_ = l_Lean_Elab_liftMacroM___redArg___lam__14(
        v_methods_5292_,
        v_____do__lift_5293_,
        v_____do__lift_5294_,
        v_____do__lift_5295_,
        v_____do__lift_5296_,
        v_x_5297_,
        v_toPure_5298_,
        v_inst_5299_,
        v___f_5300_,
        v_toBind_5301_,
        v_setNextMacroScope_5302_,
        v_inst_5303_,
        v_inst_5304_,
        v_inst_5305_,
        v_toMonadRef_5306_,
        v_inst_5307_,
        v_inst_5308_,
        v_toMonadExceptOf_5309_,
        v_getNextMacroScope_5310_,
        v_____do__lift_5311_,
    );
    return v_res_5312_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__15(
    mut v_methods_5313_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5314_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5315_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5316_: *mut crate::leanh::LeanObject,
    mut v_x_5317_: *mut crate::leanh::LeanObject,
    mut v_toPure_5318_: *mut crate::leanh::LeanObject,
    mut v_inst_5319_: *mut crate::leanh::LeanObject,
    mut v___f_5320_: *mut crate::leanh::LeanObject,
    mut v_toBind_5321_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5322_: *mut crate::leanh::LeanObject,
    mut v_inst_5323_: *mut crate::leanh::LeanObject,
    mut v_inst_5324_: *mut crate::leanh::LeanObject,
    mut v_inst_5325_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5326_: *mut crate::leanh::LeanObject,
    mut v_inst_5327_: *mut crate::leanh::LeanObject,
    mut v_inst_5328_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5329_: *mut crate::leanh::LeanObject,
    mut v_getNextMacroScope_5330_: *mut crate::leanh::LeanObject,
    mut v_getMaxRecDepth_5331_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_5321_);
    v___f_5333_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__14___boxed as *mut core::ffi::c_void,
        20,
        19,
    );
    crate::leanh::lean_closure_set(v___f_5333_, 0, v_methods_5313_);
    crate::leanh::lean_closure_set(v___f_5333_, 1, v_____do__lift_5314_);
    crate::leanh::lean_closure_set(v___f_5333_, 2, v_____do__lift_5315_);
    crate::leanh::lean_closure_set(v___f_5333_, 3, v_____do__lift_5332_);
    crate::leanh::lean_closure_set(v___f_5333_, 4, v_____do__lift_5316_);
    crate::leanh::lean_closure_set(v___f_5333_, 5, v_x_5317_);
    crate::leanh::lean_closure_set(v___f_5333_, 6, v_toPure_5318_);
    crate::leanh::lean_closure_set(v___f_5333_, 7, v_inst_5319_);
    crate::leanh::lean_closure_set(v___f_5333_, 8, v___f_5320_);
    crate::leanh::lean_closure_set(v___f_5333_, 9, v_toBind_5321_);
    crate::leanh::lean_closure_set(v___f_5333_, 10, v_setNextMacroScope_5322_);
    crate::leanh::lean_closure_set(v___f_5333_, 11, v_inst_5323_);
    crate::leanh::lean_closure_set(v___f_5333_, 12, v_inst_5324_);
    crate::leanh::lean_closure_set(v___f_5333_, 13, v_inst_5325_);
    crate::leanh::lean_closure_set(v___f_5333_, 14, v_toMonadRef_5326_);
    crate::leanh::lean_closure_set(v___f_5333_, 15, v_inst_5327_);
    crate::leanh::lean_closure_set(v___f_5333_, 16, v_inst_5328_);
    crate::leanh::lean_closure_set(v___f_5333_, 17, v_toMonadExceptOf_5329_);
    crate::leanh::lean_closure_set(v___f_5333_, 18, v_getNextMacroScope_5330_);
    v___x_5334_ = crate::leanh::lean_apply_4(
        v_toBind_5321_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getMaxRecDepth_5331_,
        v___f_5333_,
    );
    return v___x_5334_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_methods_5335_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_____do__lift_5336_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_____do__lift_5337_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_____do__lift_5338_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_x_5339_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_toPure_5340_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_5341_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___f_5342_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_toBind_5343_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_setNextMacroScope_5344_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_5345_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_5346_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_5347_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_toMonadRef_5348_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_5349_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_5350_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_toMonadExceptOf_5351_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_getNextMacroScope_5352_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_getMaxRecDepth_5353_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_____do__lift_5354_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5355_ = l_Lean_Elab_liftMacroM___redArg___lam__15(
        v_methods_5335_,
        v_____do__lift_5336_,
        v_____do__lift_5337_,
        v_____do__lift_5338_,
        v_x_5339_,
        v_toPure_5340_,
        v_inst_5341_,
        v___f_5342_,
        v_toBind_5343_,
        v_setNextMacroScope_5344_,
        v_inst_5345_,
        v_inst_5346_,
        v_inst_5347_,
        v_toMonadRef_5348_,
        v_inst_5349_,
        v_inst_5350_,
        v_toMonadExceptOf_5351_,
        v_getNextMacroScope_5352_,
        v_getMaxRecDepth_5353_,
        v_____do__lift_5354_,
    );
    return v_res_5355_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__16(
    mut v_inst_5356_: *mut crate::leanh::LeanObject,
    mut v_methods_5357_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5358_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5359_: *mut crate::leanh::LeanObject,
    mut v_x_5360_: *mut crate::leanh::LeanObject,
    mut v_toPure_5361_: *mut crate::leanh::LeanObject,
    mut v_inst_5362_: *mut crate::leanh::LeanObject,
    mut v___f_5363_: *mut crate::leanh::LeanObject,
    mut v_toBind_5364_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5365_: *mut crate::leanh::LeanObject,
    mut v_inst_5366_: *mut crate::leanh::LeanObject,
    mut v_inst_5367_: *mut crate::leanh::LeanObject,
    mut v_inst_5368_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5369_: *mut crate::leanh::LeanObject,
    mut v_inst_5370_: *mut crate::leanh::LeanObject,
    mut v_inst_5371_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5372_: *mut crate::leanh::LeanObject,
    mut v_getNextMacroScope_5373_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRecDepth_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getMaxRecDepth_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRecDepth_5375_ = crate::leanh::lean_ctor_get(v_inst_5356_, 1);
    crate::leanh::lean_inc(v_getRecDepth_5375_);
    v_getMaxRecDepth_5376_ = crate::leanh::lean_ctor_get(v_inst_5356_, 2);
    crate::leanh::lean_inc(v_getMaxRecDepth_5376_);
    crate::leanh::lean_dec_ref(v_inst_5356_);
    crate::leanh::lean_inc(v_toBind_5364_);
    v___f_5377_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__15___boxed as *mut core::ffi::c_void,
        20,
        19,
    );
    crate::leanh::lean_closure_set(v___f_5377_, 0, v_methods_5357_);
    crate::leanh::lean_closure_set(v___f_5377_, 1, v_____do__lift_5374_);
    crate::leanh::lean_closure_set(v___f_5377_, 2, v_____do__lift_5358_);
    crate::leanh::lean_closure_set(v___f_5377_, 3, v_____do__lift_5359_);
    crate::leanh::lean_closure_set(v___f_5377_, 4, v_x_5360_);
    crate::leanh::lean_closure_set(v___f_5377_, 5, v_toPure_5361_);
    crate::leanh::lean_closure_set(v___f_5377_, 6, v_inst_5362_);
    crate::leanh::lean_closure_set(v___f_5377_, 7, v___f_5363_);
    crate::leanh::lean_closure_set(v___f_5377_, 8, v_toBind_5364_);
    crate::leanh::lean_closure_set(v___f_5377_, 9, v_setNextMacroScope_5365_);
    crate::leanh::lean_closure_set(v___f_5377_, 10, v_inst_5366_);
    crate::leanh::lean_closure_set(v___f_5377_, 11, v_inst_5367_);
    crate::leanh::lean_closure_set(v___f_5377_, 12, v_inst_5368_);
    crate::leanh::lean_closure_set(v___f_5377_, 13, v_toMonadRef_5369_);
    crate::leanh::lean_closure_set(v___f_5377_, 14, v_inst_5370_);
    crate::leanh::lean_closure_set(v___f_5377_, 15, v_inst_5371_);
    crate::leanh::lean_closure_set(v___f_5377_, 16, v_toMonadExceptOf_5372_);
    crate::leanh::lean_closure_set(v___f_5377_, 17, v_getNextMacroScope_5373_);
    crate::leanh::lean_closure_set(v___f_5377_, 18, v_getMaxRecDepth_5376_);
    v___x_5378_ = crate::leanh::lean_apply_4(
        v_toBind_5364_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRecDepth_5375_,
        v___f_5377_,
    );
    return v___x_5378_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_5379_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_methods_5380_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_____do__lift_5381_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_____do__lift_5382_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_x_5383_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_toPure_5384_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_5385_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___f_5386_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_toBind_5387_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_setNextMacroScope_5388_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_5389_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_5390_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_5391_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_toMonadRef_5392_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_5393_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_5394_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_toMonadExceptOf_5395_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_getNextMacroScope_5396_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_____do__lift_5397_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5398_ = l_Lean_Elab_liftMacroM___redArg___lam__16(
        v_inst_5379_,
        v_methods_5380_,
        v_____do__lift_5381_,
        v_____do__lift_5382_,
        v_x_5383_,
        v_toPure_5384_,
        v_inst_5385_,
        v___f_5386_,
        v_toBind_5387_,
        v_setNextMacroScope_5388_,
        v_inst_5389_,
        v_inst_5390_,
        v_inst_5391_,
        v_toMonadRef_5392_,
        v_inst_5393_,
        v_inst_5394_,
        v_toMonadExceptOf_5395_,
        v_getNextMacroScope_5396_,
        v_____do__lift_5397_,
    );
    return v_res_5398_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__17(
    mut v_inst_5399_: *mut crate::leanh::LeanObject,
    mut v_methods_5400_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5401_: *mut crate::leanh::LeanObject,
    mut v_x_5402_: *mut crate::leanh::LeanObject,
    mut v_toPure_5403_: *mut crate::leanh::LeanObject,
    mut v_inst_5404_: *mut crate::leanh::LeanObject,
    mut v___f_5405_: *mut crate::leanh::LeanObject,
    mut v_toBind_5406_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5407_: *mut crate::leanh::LeanObject,
    mut v_inst_5408_: *mut crate::leanh::LeanObject,
    mut v_inst_5409_: *mut crate::leanh::LeanObject,
    mut v_inst_5410_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5411_: *mut crate::leanh::LeanObject,
    mut v_inst_5412_: *mut crate::leanh::LeanObject,
    mut v_inst_5413_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5414_: *mut crate::leanh::LeanObject,
    mut v_getNextMacroScope_5415_: *mut crate::leanh::LeanObject,
    mut v_getContext_5416_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_5406_);
    v___f_5418_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__16___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    crate::leanh::lean_closure_set(v___f_5418_, 0, v_inst_5399_);
    crate::leanh::lean_closure_set(v___f_5418_, 1, v_methods_5400_);
    crate::leanh::lean_closure_set(v___f_5418_, 2, v_____do__lift_5417_);
    crate::leanh::lean_closure_set(v___f_5418_, 3, v_____do__lift_5401_);
    crate::leanh::lean_closure_set(v___f_5418_, 4, v_x_5402_);
    crate::leanh::lean_closure_set(v___f_5418_, 5, v_toPure_5403_);
    crate::leanh::lean_closure_set(v___f_5418_, 6, v_inst_5404_);
    crate::leanh::lean_closure_set(v___f_5418_, 7, v___f_5405_);
    crate::leanh::lean_closure_set(v___f_5418_, 8, v_toBind_5406_);
    crate::leanh::lean_closure_set(v___f_5418_, 9, v_setNextMacroScope_5407_);
    crate::leanh::lean_closure_set(v___f_5418_, 10, v_inst_5408_);
    crate::leanh::lean_closure_set(v___f_5418_, 11, v_inst_5409_);
    crate::leanh::lean_closure_set(v___f_5418_, 12, v_inst_5410_);
    crate::leanh::lean_closure_set(v___f_5418_, 13, v_toMonadRef_5411_);
    crate::leanh::lean_closure_set(v___f_5418_, 14, v_inst_5412_);
    crate::leanh::lean_closure_set(v___f_5418_, 15, v_inst_5413_);
    crate::leanh::lean_closure_set(v___f_5418_, 16, v_toMonadExceptOf_5414_);
    crate::leanh::lean_closure_set(v___f_5418_, 17, v_getNextMacroScope_5415_);
    v___x_5419_ = crate::leanh::lean_apply_4(
        v_toBind_5406_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getContext_5416_,
        v___f_5418_,
    );
    return v___x_5419_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_5420_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_methods_5421_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_____do__lift_5422_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_x_5423_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_toPure_5424_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_5425_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___f_5426_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_toBind_5427_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_setNextMacroScope_5428_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_5429_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_5430_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_5431_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toMonadRef_5432_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_5433_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_5434_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_toMonadExceptOf_5435_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_getNextMacroScope_5436_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_getContext_5437_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_____do__lift_5438_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5439_ = l_Lean_Elab_liftMacroM___redArg___lam__17(
        v_inst_5420_,
        v_methods_5421_,
        v_____do__lift_5422_,
        v_x_5423_,
        v_toPure_5424_,
        v_inst_5425_,
        v___f_5426_,
        v_toBind_5427_,
        v_setNextMacroScope_5428_,
        v_inst_5429_,
        v_inst_5430_,
        v_inst_5431_,
        v_toMonadRef_5432_,
        v_inst_5433_,
        v_inst_5434_,
        v_toMonadExceptOf_5435_,
        v_getNextMacroScope_5436_,
        v_getContext_5437_,
        v_____do__lift_5438_,
    );
    return v_res_5439_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__18(
    mut v_toMonadQuotation_5440_: *mut crate::leanh::LeanObject,
    mut v_inst_5441_: *mut crate::leanh::LeanObject,
    mut v_methods_5442_: *mut crate::leanh::LeanObject,
    mut v_x_5443_: *mut crate::leanh::LeanObject,
    mut v_toPure_5444_: *mut crate::leanh::LeanObject,
    mut v_inst_5445_: *mut crate::leanh::LeanObject,
    mut v___f_5446_: *mut crate::leanh::LeanObject,
    mut v_toBind_5447_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5448_: *mut crate::leanh::LeanObject,
    mut v_inst_5449_: *mut crate::leanh::LeanObject,
    mut v_inst_5450_: *mut crate::leanh::LeanObject,
    mut v_inst_5451_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5452_: *mut crate::leanh::LeanObject,
    mut v_inst_5453_: *mut crate::leanh::LeanObject,
    mut v_inst_5454_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5455_: *mut crate::leanh::LeanObject,
    mut v_getNextMacroScope_5456_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCurrMacroScope_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getContext_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_5458_ = crate::leanh::lean_ctor_get(v_toMonadQuotation_5440_, 1);
    crate::leanh::lean_inc(v_getCurrMacroScope_5458_);
    v_getContext_5459_ = crate::leanh::lean_ctor_get(v_toMonadQuotation_5440_, 2);
    crate::leanh::lean_inc(v_getContext_5459_);
    crate::leanh::lean_dec_ref(v_toMonadQuotation_5440_);
    crate::leanh::lean_inc(v_toBind_5447_);
    v___f_5460_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__17___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    crate::leanh::lean_closure_set(v___f_5460_, 0, v_inst_5441_);
    crate::leanh::lean_closure_set(v___f_5460_, 1, v_methods_5442_);
    crate::leanh::lean_closure_set(v___f_5460_, 2, v_____do__lift_5457_);
    crate::leanh::lean_closure_set(v___f_5460_, 3, v_x_5443_);
    crate::leanh::lean_closure_set(v___f_5460_, 4, v_toPure_5444_);
    crate::leanh::lean_closure_set(v___f_5460_, 5, v_inst_5445_);
    crate::leanh::lean_closure_set(v___f_5460_, 6, v___f_5446_);
    crate::leanh::lean_closure_set(v___f_5460_, 7, v_toBind_5447_);
    crate::leanh::lean_closure_set(v___f_5460_, 8, v_setNextMacroScope_5448_);
    crate::leanh::lean_closure_set(v___f_5460_, 9, v_inst_5449_);
    crate::leanh::lean_closure_set(v___f_5460_, 10, v_inst_5450_);
    crate::leanh::lean_closure_set(v___f_5460_, 11, v_inst_5451_);
    crate::leanh::lean_closure_set(v___f_5460_, 12, v_toMonadRef_5452_);
    crate::leanh::lean_closure_set(v___f_5460_, 13, v_inst_5453_);
    crate::leanh::lean_closure_set(v___f_5460_, 14, v_inst_5454_);
    crate::leanh::lean_closure_set(v___f_5460_, 15, v_toMonadExceptOf_5455_);
    crate::leanh::lean_closure_set(v___f_5460_, 16, v_getNextMacroScope_5456_);
    crate::leanh::lean_closure_set(v___f_5460_, 17, v_getContext_5459_);
    v___x_5461_ = crate::leanh::lean_apply_4(
        v_toBind_5447_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrMacroScope_5458_,
        v___f_5460_,
    );
    return v___x_5461_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toMonadQuotation_5462_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_5463_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_methods_5464_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_x_5465_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_toPure_5466_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_5467_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___f_5468_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_toBind_5469_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_setNextMacroScope_5470_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_5471_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_5472_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_5473_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toMonadRef_5474_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_5475_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_5476_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_toMonadExceptOf_5477_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_getNextMacroScope_5478_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_____do__lift_5479_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5480_ = l_Lean_Elab_liftMacroM___redArg___lam__18(
        v_toMonadQuotation_5462_,
        v_inst_5463_,
        v_methods_5464_,
        v_x_5465_,
        v_toPure_5466_,
        v_inst_5467_,
        v___f_5468_,
        v_toBind_5469_,
        v_setNextMacroScope_5470_,
        v_inst_5471_,
        v_inst_5472_,
        v_inst_5473_,
        v_toMonadRef_5474_,
        v_inst_5475_,
        v_inst_5476_,
        v_toMonadExceptOf_5477_,
        v_getNextMacroScope_5478_,
        v_____do__lift_5479_,
    );
    return v_res_5480_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__19(
    mut v_toMonadRef_5481_: *mut crate::leanh::LeanObject,
    mut v_env_5482_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5483_: *mut crate::leanh::LeanObject,
    mut v_opts_5484_: *mut crate::leanh::LeanObject,
    mut v___x_5485_: *mut crate::leanh::LeanObject,
    mut v___f_5486_: *mut crate::leanh::LeanObject,
    mut v___f_5487_: *mut crate::leanh::LeanObject,
    mut v_toMonadQuotation_5488_: *mut crate::leanh::LeanObject,
    mut v_inst_5489_: *mut crate::leanh::LeanObject,
    mut v_x_5490_: *mut crate::leanh::LeanObject,
    mut v_toPure_5491_: *mut crate::leanh::LeanObject,
    mut v_inst_5492_: *mut crate::leanh::LeanObject,
    mut v___f_5493_: *mut crate::leanh::LeanObject,
    mut v_toBind_5494_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5495_: *mut crate::leanh::LeanObject,
    mut v_inst_5496_: *mut crate::leanh::LeanObject,
    mut v_inst_5497_: *mut crate::leanh::LeanObject,
    mut v_inst_5498_: *mut crate::leanh::LeanObject,
    mut v_inst_5499_: *mut crate::leanh::LeanObject,
    mut v_inst_5500_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5501_: *mut crate::leanh::LeanObject,
    mut v_getNextMacroScope_5502_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_5504_ = crate::leanh::lean_ctor_get(v_toMonadRef_5481_, 0);
    crate::leanh::lean_inc(v_getRef_5504_);
    crate::leanh::lean_inc(v_openDecls_5503_);
    crate::leanh::lean_inc_n(v_currNamespace_5483_, 2);
    crate::leanh::lean_inc_ref(v_env_5482_);
    v___f_5505_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__6___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5505_, 0, v_env_5482_);
    crate::leanh::lean_closure_set(v___f_5505_, 1, v_currNamespace_5483_);
    crate::leanh::lean_closure_set(v___f_5505_, 2, v_openDecls_5503_);
    v___f_5506_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__7___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5506_, 0, v_env_5482_);
    crate::leanh::lean_closure_set(v___f_5506_, 1, v_opts_5484_);
    crate::leanh::lean_closure_set(v___f_5506_, 2, v_currNamespace_5483_);
    crate::leanh::lean_closure_set(v___f_5506_, 3, v_openDecls_5503_);
    v___x_5507_ =
        crate::leanh::lean_alloc_closure(l_ReaderT_pure___boxed as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___x_5507_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5507_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5507_, 2, v___x_5485_);
    crate::leanh::lean_closure_set(v___x_5507_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5507_, 4, v_currNamespace_5483_);
    v_methods_5508_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v_methods_5508_, 0, v___f_5486_);
    crate::leanh::lean_ctor_set(v_methods_5508_, 1, v___x_5507_);
    crate::leanh::lean_ctor_set(v_methods_5508_, 2, v___f_5487_);
    crate::leanh::lean_ctor_set(v_methods_5508_, 3, v___f_5505_);
    crate::leanh::lean_ctor_set(v_methods_5508_, 4, v___f_5506_);
    crate::leanh::lean_inc(v_toBind_5494_);
    v___f_5509_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__18___boxed as *mut core::ffi::c_void,
        18,
        17,
    );
    crate::leanh::lean_closure_set(v___f_5509_, 0, v_toMonadQuotation_5488_);
    crate::leanh::lean_closure_set(v___f_5509_, 1, v_inst_5489_);
    crate::leanh::lean_closure_set(v___f_5509_, 2, v_methods_5508_);
    crate::leanh::lean_closure_set(v___f_5509_, 3, v_x_5490_);
    crate::leanh::lean_closure_set(v___f_5509_, 4, v_toPure_5491_);
    crate::leanh::lean_closure_set(v___f_5509_, 5, v_inst_5492_);
    crate::leanh::lean_closure_set(v___f_5509_, 6, v___f_5493_);
    crate::leanh::lean_closure_set(v___f_5509_, 7, v_toBind_5494_);
    crate::leanh::lean_closure_set(v___f_5509_, 8, v_setNextMacroScope_5495_);
    crate::leanh::lean_closure_set(v___f_5509_, 9, v_inst_5496_);
    crate::leanh::lean_closure_set(v___f_5509_, 10, v_inst_5497_);
    crate::leanh::lean_closure_set(v___f_5509_, 11, v_inst_5498_);
    crate::leanh::lean_closure_set(v___f_5509_, 12, v_toMonadRef_5481_);
    crate::leanh::lean_closure_set(v___f_5509_, 13, v_inst_5499_);
    crate::leanh::lean_closure_set(v___f_5509_, 14, v_inst_5500_);
    crate::leanh::lean_closure_set(v___f_5509_, 15, v_toMonadExceptOf_5501_);
    crate::leanh::lean_closure_set(v___f_5509_, 16, v_getNextMacroScope_5502_);
    v___x_5510_ = crate::leanh::lean_apply_4(
        v_toBind_5494_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_5504_,
        v___f_5509_,
    );
    return v___x_5510_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toMonadRef_5511_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_env_5512_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_currNamespace_5513_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_opts_5514_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_5515_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___f_5516_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___f_5517_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_toMonadQuotation_5518_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_5519_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_x_5520_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_toPure_5521_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_5522_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___f_5523_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_toBind_5524_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_setNextMacroScope_5525_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_5526_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_5527_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_inst_5528_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_inst_5529_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_inst_5530_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_toMonadExceptOf_5531_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_getNextMacroScope_5532_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_openDecls_5533_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_res_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5534_ = l_Lean_Elab_liftMacroM___redArg___lam__19(
        v_toMonadRef_5511_,
        v_env_5512_,
        v_currNamespace_5513_,
        v_opts_5514_,
        v___x_5515_,
        v___f_5516_,
        v___f_5517_,
        v_toMonadQuotation_5518_,
        v_inst_5519_,
        v_x_5520_,
        v_toPure_5521_,
        v_inst_5522_,
        v___f_5523_,
        v_toBind_5524_,
        v_setNextMacroScope_5525_,
        v_inst_5526_,
        v_inst_5527_,
        v_inst_5528_,
        v_inst_5529_,
        v_inst_5530_,
        v_toMonadExceptOf_5531_,
        v_getNextMacroScope_5532_,
        v_openDecls_5533_,
    );
    return v_res_5534_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__20(
    mut v_toMonadRef_5535_: *mut crate::leanh::LeanObject,
    mut v_env_5536_: *mut crate::leanh::LeanObject,
    mut v_opts_5537_: *mut crate::leanh::LeanObject,
    mut v___x_5538_: *mut crate::leanh::LeanObject,
    mut v___f_5539_: *mut crate::leanh::LeanObject,
    mut v___f_5540_: *mut crate::leanh::LeanObject,
    mut v_toMonadQuotation_5541_: *mut crate::leanh::LeanObject,
    mut v_inst_5542_: *mut crate::leanh::LeanObject,
    mut v_x_5543_: *mut crate::leanh::LeanObject,
    mut v_toPure_5544_: *mut crate::leanh::LeanObject,
    mut v_inst_5545_: *mut crate::leanh::LeanObject,
    mut v___f_5546_: *mut crate::leanh::LeanObject,
    mut v_toBind_5547_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5548_: *mut crate::leanh::LeanObject,
    mut v_inst_5549_: *mut crate::leanh::LeanObject,
    mut v_inst_5550_: *mut crate::leanh::LeanObject,
    mut v_inst_5551_: *mut crate::leanh::LeanObject,
    mut v_inst_5552_: *mut crate::leanh::LeanObject,
    mut v_inst_5553_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5554_: *mut crate::leanh::LeanObject,
    mut v_getNextMacroScope_5555_: *mut crate::leanh::LeanObject,
    mut v_getOpenDecls_5556_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_5547_);
    v___f_5558_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__19___boxed as *mut core::ffi::c_void,
        23,
        22,
    );
    crate::leanh::lean_closure_set(v___f_5558_, 0, v_toMonadRef_5535_);
    crate::leanh::lean_closure_set(v___f_5558_, 1, v_env_5536_);
    crate::leanh::lean_closure_set(v___f_5558_, 2, v_currNamespace_5557_);
    crate::leanh::lean_closure_set(v___f_5558_, 3, v_opts_5537_);
    crate::leanh::lean_closure_set(v___f_5558_, 4, v___x_5538_);
    crate::leanh::lean_closure_set(v___f_5558_, 5, v___f_5539_);
    crate::leanh::lean_closure_set(v___f_5558_, 6, v___f_5540_);
    crate::leanh::lean_closure_set(v___f_5558_, 7, v_toMonadQuotation_5541_);
    crate::leanh::lean_closure_set(v___f_5558_, 8, v_inst_5542_);
    crate::leanh::lean_closure_set(v___f_5558_, 9, v_x_5543_);
    crate::leanh::lean_closure_set(v___f_5558_, 10, v_toPure_5544_);
    crate::leanh::lean_closure_set(v___f_5558_, 11, v_inst_5545_);
    crate::leanh::lean_closure_set(v___f_5558_, 12, v___f_5546_);
    crate::leanh::lean_closure_set(v___f_5558_, 13, v_toBind_5547_);
    crate::leanh::lean_closure_set(v___f_5558_, 14, v_setNextMacroScope_5548_);
    crate::leanh::lean_closure_set(v___f_5558_, 15, v_inst_5549_);
    crate::leanh::lean_closure_set(v___f_5558_, 16, v_inst_5550_);
    crate::leanh::lean_closure_set(v___f_5558_, 17, v_inst_5551_);
    crate::leanh::lean_closure_set(v___f_5558_, 18, v_inst_5552_);
    crate::leanh::lean_closure_set(v___f_5558_, 19, v_inst_5553_);
    crate::leanh::lean_closure_set(v___f_5558_, 20, v_toMonadExceptOf_5554_);
    crate::leanh::lean_closure_set(v___f_5558_, 21, v_getNextMacroScope_5555_);
    v___x_5559_ = crate::leanh::lean_apply_4(
        v_toBind_5547_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getOpenDecls_5556_,
        v___f_5558_,
    );
    return v___x_5559_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toMonadRef_5560_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_env_5561_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_opts_5562_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_5563_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_5564_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___f_5565_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_toMonadQuotation_5566_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_inst_5567_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_x_5568_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_toPure_5569_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_5570_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___f_5571_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toBind_5572_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_setNextMacroScope_5573_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_5574_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_5575_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_5576_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_inst_5577_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_inst_5578_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_toMonadExceptOf_5579_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_getNextMacroScope_5580_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_getOpenDecls_5581_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_currNamespace_5582_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_res_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_Elab_liftMacroM___redArg___lam__20(
        v_toMonadRef_5560_,
        v_env_5561_,
        v_opts_5562_,
        v___x_5563_,
        v___f_5564_,
        v___f_5565_,
        v_toMonadQuotation_5566_,
        v_inst_5567_,
        v_x_5568_,
        v_toPure_5569_,
        v_inst_5570_,
        v___f_5571_,
        v_toBind_5572_,
        v_setNextMacroScope_5573_,
        v_inst_5574_,
        v_inst_5575_,
        v_inst_5576_,
        v_inst_5577_,
        v_inst_5578_,
        v_toMonadExceptOf_5579_,
        v_getNextMacroScope_5580_,
        v_getOpenDecls_5581_,
        v_currNamespace_5582_,
    );
    return v_res_5583_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__21(
    mut v_inst_5584_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5585_: *mut crate::leanh::LeanObject,
    mut v_env_5586_: *mut crate::leanh::LeanObject,
    mut v___x_5587_: *mut crate::leanh::LeanObject,
    mut v___f_5588_: *mut crate::leanh::LeanObject,
    mut v___f_5589_: *mut crate::leanh::LeanObject,
    mut v_toMonadQuotation_5590_: *mut crate::leanh::LeanObject,
    mut v_inst_5591_: *mut crate::leanh::LeanObject,
    mut v_x_5592_: *mut crate::leanh::LeanObject,
    mut v_toPure_5593_: *mut crate::leanh::LeanObject,
    mut v_inst_5594_: *mut crate::leanh::LeanObject,
    mut v___f_5595_: *mut crate::leanh::LeanObject,
    mut v_toBind_5596_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5597_: *mut crate::leanh::LeanObject,
    mut v_inst_5598_: *mut crate::leanh::LeanObject,
    mut v_inst_5599_: *mut crate::leanh::LeanObject,
    mut v_inst_5600_: *mut crate::leanh::LeanObject,
    mut v_inst_5601_: *mut crate::leanh::LeanObject,
    mut v_inst_5602_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5603_: *mut crate::leanh::LeanObject,
    mut v_getNextMacroScope_5604_: *mut crate::leanh::LeanObject,
    mut v_opts_5605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCurrNamespace_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCurrNamespace_5606_ = crate::leanh::lean_ctor_get(v_inst_5584_, 0);
    crate::leanh::lean_inc(v_getCurrNamespace_5606_);
    v_getOpenDecls_5607_ = crate::leanh::lean_ctor_get(v_inst_5584_, 1);
    crate::leanh::lean_inc(v_getOpenDecls_5607_);
    crate::leanh::lean_dec_ref(v_inst_5584_);
    crate::leanh::lean_inc(v_toBind_5596_);
    v___f_5608_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__20___boxed as *mut core::ffi::c_void,
        23,
        22,
    );
    crate::leanh::lean_closure_set(v___f_5608_, 0, v_toMonadRef_5585_);
    crate::leanh::lean_closure_set(v___f_5608_, 1, v_env_5586_);
    crate::leanh::lean_closure_set(v___f_5608_, 2, v_opts_5605_);
    crate::leanh::lean_closure_set(v___f_5608_, 3, v___x_5587_);
    crate::leanh::lean_closure_set(v___f_5608_, 4, v___f_5588_);
    crate::leanh::lean_closure_set(v___f_5608_, 5, v___f_5589_);
    crate::leanh::lean_closure_set(v___f_5608_, 6, v_toMonadQuotation_5590_);
    crate::leanh::lean_closure_set(v___f_5608_, 7, v_inst_5591_);
    crate::leanh::lean_closure_set(v___f_5608_, 8, v_x_5592_);
    crate::leanh::lean_closure_set(v___f_5608_, 9, v_toPure_5593_);
    crate::leanh::lean_closure_set(v___f_5608_, 10, v_inst_5594_);
    crate::leanh::lean_closure_set(v___f_5608_, 11, v___f_5595_);
    crate::leanh::lean_closure_set(v___f_5608_, 12, v_toBind_5596_);
    crate::leanh::lean_closure_set(v___f_5608_, 13, v_setNextMacroScope_5597_);
    crate::leanh::lean_closure_set(v___f_5608_, 14, v_inst_5598_);
    crate::leanh::lean_closure_set(v___f_5608_, 15, v_inst_5599_);
    crate::leanh::lean_closure_set(v___f_5608_, 16, v_inst_5600_);
    crate::leanh::lean_closure_set(v___f_5608_, 17, v_inst_5601_);
    crate::leanh::lean_closure_set(v___f_5608_, 18, v_inst_5602_);
    crate::leanh::lean_closure_set(v___f_5608_, 19, v_toMonadExceptOf_5603_);
    crate::leanh::lean_closure_set(v___f_5608_, 20, v_getNextMacroScope_5604_);
    crate::leanh::lean_closure_set(v___f_5608_, 21, v_getOpenDecls_5607_);
    v___x_5609_ = crate::leanh::lean_apply_4(
        v_toBind_5596_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrNamespace_5606_,
        v___f_5608_,
    );
    return v___x_5609_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_5610_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_toMonadRef_5611_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_env_5612_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_5613_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_5614_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___f_5615_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_toMonadQuotation_5616_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_inst_5617_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_x_5618_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_toPure_5619_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_5620_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___f_5621_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toBind_5622_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_setNextMacroScope_5623_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_5624_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_5625_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_5626_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_inst_5627_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_inst_5628_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_toMonadExceptOf_5629_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_getNextMacroScope_5630_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_opts_5631_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_res_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5632_ = l_Lean_Elab_liftMacroM___redArg___lam__21(
        v_inst_5610_,
        v_toMonadRef_5611_,
        v_env_5612_,
        v___x_5613_,
        v___f_5614_,
        v___f_5615_,
        v_toMonadQuotation_5616_,
        v_inst_5617_,
        v_x_5618_,
        v_toPure_5619_,
        v_inst_5620_,
        v___f_5621_,
        v_toBind_5622_,
        v_setNextMacroScope_5623_,
        v_inst_5624_,
        v_inst_5625_,
        v_inst_5626_,
        v_inst_5627_,
        v_inst_5628_,
        v_toMonadExceptOf_5629_,
        v_getNextMacroScope_5630_,
        v_opts_5631_,
    );
    return v_res_5632_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__22(
    mut v___x_5633_: *mut crate::leanh::LeanObject,
    mut v___x_5634_: *mut crate::leanh::LeanObject,
    mut v_inst_5635_: *mut crate::leanh::LeanObject,
    mut v_toMonadRef_5636_: *mut crate::leanh::LeanObject,
    mut v___x_5637_: *mut crate::leanh::LeanObject,
    mut v_toMonadQuotation_5638_: *mut crate::leanh::LeanObject,
    mut v_inst_5639_: *mut crate::leanh::LeanObject,
    mut v_x_5640_: *mut crate::leanh::LeanObject,
    mut v_toPure_5641_: *mut crate::leanh::LeanObject,
    mut v_inst_5642_: *mut crate::leanh::LeanObject,
    mut v___f_5643_: *mut crate::leanh::LeanObject,
    mut v_toBind_5644_: *mut crate::leanh::LeanObject,
    mut v_setNextMacroScope_5645_: *mut crate::leanh::LeanObject,
    mut v_inst_5646_: *mut crate::leanh::LeanObject,
    mut v_inst_5647_: *mut crate::leanh::LeanObject,
    mut v_inst_5648_: *mut crate::leanh::LeanObject,
    mut v_inst_5649_: *mut crate::leanh::LeanObject,
    mut v_inst_5650_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_5651_: *mut crate::leanh::LeanObject,
    mut v_getNextMacroScope_5652_: *mut crate::leanh::LeanObject,
    mut v_env_5653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_env_5653_, 2);
    v___f_5654_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__4___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5654_, 0, v_env_5653_);
    crate::leanh::lean_closure_set(v___f_5654_, 1, v___x_5633_);
    crate::leanh::lean_closure_set(v___f_5654_, 2, v___x_5634_);
    v___f_5655_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__5___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5655_, 0, v_env_5653_);
    crate::leanh::lean_inc(v_inst_5648_);
    crate::leanh::lean_inc(v_toBind_5644_);
    v___f_5656_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__21___boxed as *mut core::ffi::c_void,
        22,
        21,
    );
    crate::leanh::lean_closure_set(v___f_5656_, 0, v_inst_5635_);
    crate::leanh::lean_closure_set(v___f_5656_, 1, v_toMonadRef_5636_);
    crate::leanh::lean_closure_set(v___f_5656_, 2, v_env_5653_);
    crate::leanh::lean_closure_set(v___f_5656_, 3, v___x_5637_);
    crate::leanh::lean_closure_set(v___f_5656_, 4, v___f_5654_);
    crate::leanh::lean_closure_set(v___f_5656_, 5, v___f_5655_);
    crate::leanh::lean_closure_set(v___f_5656_, 6, v_toMonadQuotation_5638_);
    crate::leanh::lean_closure_set(v___f_5656_, 7, v_inst_5639_);
    crate::leanh::lean_closure_set(v___f_5656_, 8, v_x_5640_);
    crate::leanh::lean_closure_set(v___f_5656_, 9, v_toPure_5641_);
    crate::leanh::lean_closure_set(v___f_5656_, 10, v_inst_5642_);
    crate::leanh::lean_closure_set(v___f_5656_, 11, v___f_5643_);
    crate::leanh::lean_closure_set(v___f_5656_, 12, v_toBind_5644_);
    crate::leanh::lean_closure_set(v___f_5656_, 13, v_setNextMacroScope_5645_);
    crate::leanh::lean_closure_set(v___f_5656_, 14, v_inst_5646_);
    crate::leanh::lean_closure_set(v___f_5656_, 15, v_inst_5647_);
    crate::leanh::lean_closure_set(v___f_5656_, 16, v_inst_5648_);
    crate::leanh::lean_closure_set(v___f_5656_, 17, v_inst_5649_);
    crate::leanh::lean_closure_set(v___f_5656_, 18, v_inst_5650_);
    crate::leanh::lean_closure_set(v___f_5656_, 19, v_toMonadExceptOf_5651_);
    crate::leanh::lean_closure_set(v___f_5656_, 20, v_getNextMacroScope_5652_);
    v___x_5657_ = crate::leanh::lean_apply_4(
        v_toBind_5644_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5648_,
        v___f_5656_,
    );
    return v___x_5657_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5658_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_5659_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_5660_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_toMonadRef_5661_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_5662_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_toMonadQuotation_5663_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_5664_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_x_5665_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_toPure_5666_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_5667_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___f_5668_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_toBind_5669_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_setNextMacroScope_5670_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_5671_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_5672_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_5673_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_5674_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_inst_5675_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_toMonadExceptOf_5676_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_getNextMacroScope_5677_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_env_5678_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_res_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5679_ = l_Lean_Elab_liftMacroM___redArg___lam__22(
        v___x_5658_,
        v___x_5659_,
        v_inst_5660_,
        v_toMonadRef_5661_,
        v___x_5662_,
        v_toMonadQuotation_5663_,
        v_inst_5664_,
        v_x_5665_,
        v_toPure_5666_,
        v_inst_5667_,
        v___f_5668_,
        v_toBind_5669_,
        v_setNextMacroScope_5670_,
        v_inst_5671_,
        v_inst_5672_,
        v_inst_5673_,
        v_inst_5674_,
        v_inst_5675_,
        v_toMonadExceptOf_5676_,
        v_getNextMacroScope_5677_,
        v_env_5678_,
    );
    return v_res_5679_;
}
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5699_ = l_EStateM_nonBacktrackable(crate::leanh::lean_box(0));
    return v___x_5699_;
}
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5700_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__10_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__10,
    );
    v___x_5701_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_5700_);
    return v___x_5701_;
}
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5702_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__11_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__11,
    );
    v___f_5703_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5703_, 0, v___x_5702_);
    return v___f_5703_;
}
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5704_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__11_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__11,
    );
    v___f_5705_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5705_, 0, v___x_5704_);
    return v___f_5705_;
}
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v___f_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5706_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__13_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__13,
    );
    v___f_5707_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__12_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__12,
    );
    v___x_5708_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5708_, 0, v___f_5707_);
    crate::leanh::lean_ctor_set(v___x_5708_, 1, v___f_5706_);
    return v___x_5708_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg(
    mut v_inst_5711_: *mut crate::leanh::LeanObject,
    mut v_inst_5712_: *mut crate::leanh::LeanObject,
    mut v_inst_5713_: *mut crate::leanh::LeanObject,
    mut v_inst_5714_: *mut crate::leanh::LeanObject,
    mut v_inst_5715_: *mut crate::leanh::LeanObject,
    mut v_inst_5716_: *mut crate::leanh::LeanObject,
    mut v_inst_5717_: *mut crate::leanh::LeanObject,
    mut v_inst_5718_: *mut crate::leanh::LeanObject,
    mut v_inst_5719_: *mut crate::leanh::LeanObject,
    mut v_x_5720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadExceptOf_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadQuotation_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getNextMacroScope_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_setNextMacroScope_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5721_ = l_Lean_Elab_liftMacroM___redArg___closed__9;
    v___x_5722_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__14_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__14,
    );
    v_toApplicative_5723_ = crate::leanh::lean_ctor_get(v_inst_5711_, 0);
    v_toBind_5724_ = crate::leanh::lean_ctor_get(v_inst_5711_, 1);
    crate::leanh::lean_inc_n(v_toBind_5724_, 3);
    v_getEnv_5725_ = crate::leanh::lean_ctor_get(v_inst_5713_, 0);
    crate::leanh::lean_inc(v_getEnv_5725_);
    v_toMonadExceptOf_5726_ = crate::leanh::lean_ctor_get(v_inst_5715_, 0);
    crate::leanh::lean_inc_ref(v_toMonadExceptOf_5726_);
    v_toMonadRef_5727_ = crate::leanh::lean_ctor_get(v_inst_5715_, 1);
    crate::leanh::lean_inc_ref_n(v_toMonadRef_5727_, 2);
    v_toMonadQuotation_5728_ = crate::leanh::lean_ctor_get(v_inst_5712_, 0);
    crate::leanh::lean_inc_ref(v_toMonadQuotation_5728_);
    v_getNextMacroScope_5729_ = crate::leanh::lean_ctor_get(v_inst_5712_, 1);
    crate::leanh::lean_inc(v_getNextMacroScope_5729_);
    v_setNextMacroScope_5730_ = crate::leanh::lean_ctor_get(v_inst_5712_, 2);
    crate::leanh::lean_inc(v_setNextMacroScope_5730_);
    crate::leanh::lean_dec_ref(v_inst_5712_);
    v_toPure_5731_ = crate::leanh::lean_ctor_get(v_toApplicative_5723_, 1);
    crate::leanh::lean_inc_n(v_toPure_5731_, 2);
    v___x_5732_ = l_Lean_Elab_liftMacroM___redArg___closed__15;
    crate::leanh::lean_inc(v_inst_5718_);
    crate::leanh::lean_inc(v_inst_5719_);
    crate::leanh::lean_inc_ref(v_inst_5711_);
    crate::leanh::lean_inc_ref(v_inst_5717_);
    v___f_5733_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_5733_, 0, v_inst_5717_);
    crate::leanh::lean_closure_set(v___f_5733_, 1, v_toPure_5731_);
    crate::leanh::lean_closure_set(v___f_5733_, 2, v_inst_5711_);
    crate::leanh::lean_closure_set(v___f_5733_, 3, v_toMonadRef_5727_);
    crate::leanh::lean_closure_set(v___f_5733_, 4, v_inst_5719_);
    crate::leanh::lean_closure_set(v___f_5733_, 5, v_toBind_5724_);
    crate::leanh::lean_closure_set(v___f_5733_, 6, v_inst_5718_);
    v___f_5734_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__22___boxed as *mut core::ffi::c_void,
        21,
        20,
    );
    crate::leanh::lean_closure_set(v___f_5734_, 0, v___x_5722_);
    crate::leanh::lean_closure_set(v___f_5734_, 1, v___x_5732_);
    crate::leanh::lean_closure_set(v___f_5734_, 2, v_inst_5716_);
    crate::leanh::lean_closure_set(v___f_5734_, 3, v_toMonadRef_5727_);
    crate::leanh::lean_closure_set(v___f_5734_, 4, v___x_5721_);
    crate::leanh::lean_closure_set(v___f_5734_, 5, v_toMonadQuotation_5728_);
    crate::leanh::lean_closure_set(v___f_5734_, 6, v_inst_5714_);
    crate::leanh::lean_closure_set(v___f_5734_, 7, v_x_5720_);
    crate::leanh::lean_closure_set(v___f_5734_, 8, v_toPure_5731_);
    crate::leanh::lean_closure_set(v___f_5734_, 9, v_inst_5711_);
    crate::leanh::lean_closure_set(v___f_5734_, 10, v___f_5733_);
    crate::leanh::lean_closure_set(v___f_5734_, 11, v_toBind_5724_);
    crate::leanh::lean_closure_set(v___f_5734_, 12, v_setNextMacroScope_5730_);
    crate::leanh::lean_closure_set(v___f_5734_, 13, v_inst_5713_);
    crate::leanh::lean_closure_set(v___f_5734_, 14, v_inst_5717_);
    crate::leanh::lean_closure_set(v___f_5734_, 15, v_inst_5718_);
    crate::leanh::lean_closure_set(v___f_5734_, 16, v_inst_5719_);
    crate::leanh::lean_closure_set(v___f_5734_, 17, v_inst_5715_);
    crate::leanh::lean_closure_set(v___f_5734_, 18, v_toMonadExceptOf_5726_);
    crate::leanh::lean_closure_set(v___f_5734_, 19, v_getNextMacroScope_5729_);
    v___x_5735_ = crate::leanh::lean_apply_4(
        v_toBind_5724_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_5725_,
        v___f_5734_,
    );
    return v___x_5735_;
}
pub unsafe fn l_Lean_Elab_liftMacroM(
    mut v_m_5736_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5737_: *mut crate::leanh::LeanObject,
    mut v_inst_5738_: *mut crate::leanh::LeanObject,
    mut v_inst_5739_: *mut crate::leanh::LeanObject,
    mut v_inst_5740_: *mut crate::leanh::LeanObject,
    mut v_inst_5741_: *mut crate::leanh::LeanObject,
    mut v_inst_5742_: *mut crate::leanh::LeanObject,
    mut v_inst_5743_: *mut crate::leanh::LeanObject,
    mut v_inst_5744_: *mut crate::leanh::LeanObject,
    mut v_inst_5745_: *mut crate::leanh::LeanObject,
    mut v_inst_5746_: *mut crate::leanh::LeanObject,
    mut v_inst_5747_: *mut crate::leanh::LeanObject,
    mut v_x_5748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5749_ = l_Lean_Elab_liftMacroM___redArg(
        v_inst_5738_,
        v_inst_5739_,
        v_inst_5740_,
        v_inst_5741_,
        v_inst_5742_,
        v_inst_5743_,
        v_inst_5744_,
        v_inst_5745_,
        v_inst_5746_,
        v_x_5748_,
    );
    return v___x_5749_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___boxed(
    mut v_m_5750_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5751_: *mut crate::leanh::LeanObject,
    mut v_inst_5752_: *mut crate::leanh::LeanObject,
    mut v_inst_5753_: *mut crate::leanh::LeanObject,
    mut v_inst_5754_: *mut crate::leanh::LeanObject,
    mut v_inst_5755_: *mut crate::leanh::LeanObject,
    mut v_inst_5756_: *mut crate::leanh::LeanObject,
    mut v_inst_5757_: *mut crate::leanh::LeanObject,
    mut v_inst_5758_: *mut crate::leanh::LeanObject,
    mut v_inst_5759_: *mut crate::leanh::LeanObject,
    mut v_inst_5760_: *mut crate::leanh::LeanObject,
    mut v_inst_5761_: *mut crate::leanh::LeanObject,
    mut v_x_5762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5763_ = l_Lean_Elab_liftMacroM(
        v_m_5750_,
        v_00_u03b1_5751_,
        v_inst_5752_,
        v_inst_5753_,
        v_inst_5754_,
        v_inst_5755_,
        v_inst_5756_,
        v_inst_5757_,
        v_inst_5758_,
        v_inst_5759_,
        v_inst_5760_,
        v_inst_5761_,
        v_x_5762_,
    );
    crate::leanh::lean_dec(v_inst_5761_);
    return v_res_5763_;
}
pub unsafe fn l_Lean_Elab_adaptMacro___redArg(
    mut v_inst_5764_: *mut crate::leanh::LeanObject,
    mut v_inst_5765_: *mut crate::leanh::LeanObject,
    mut v_inst_5766_: *mut crate::leanh::LeanObject,
    mut v_inst_5767_: *mut crate::leanh::LeanObject,
    mut v_inst_5768_: *mut crate::leanh::LeanObject,
    mut v_inst_5769_: *mut crate::leanh::LeanObject,
    mut v_inst_5770_: *mut crate::leanh::LeanObject,
    mut v_inst_5771_: *mut crate::leanh::LeanObject,
    mut v_inst_5772_: *mut crate::leanh::LeanObject,
    mut v_x_5773_: *mut crate::leanh::LeanObject,
    mut v_stx_5774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5775_ = crate::leanh::lean_apply_1(v_x_5773_, v_stx_5774_);
    v___x_5776_ = l_Lean_Elab_liftMacroM___redArg(
        v_inst_5764_,
        v_inst_5765_,
        v_inst_5766_,
        v_inst_5767_,
        v_inst_5768_,
        v_inst_5769_,
        v_inst_5770_,
        v_inst_5771_,
        v_inst_5772_,
        v___x_5775_,
    );
    return v___x_5776_;
}
pub unsafe fn l_Lean_Elab_adaptMacro(
    mut v_m_5777_: *mut crate::leanh::LeanObject,
    mut v_inst_5778_: *mut crate::leanh::LeanObject,
    mut v_inst_5779_: *mut crate::leanh::LeanObject,
    mut v_inst_5780_: *mut crate::leanh::LeanObject,
    mut v_inst_5781_: *mut crate::leanh::LeanObject,
    mut v_inst_5782_: *mut crate::leanh::LeanObject,
    mut v_inst_5783_: *mut crate::leanh::LeanObject,
    mut v_inst_5784_: *mut crate::leanh::LeanObject,
    mut v_inst_5785_: *mut crate::leanh::LeanObject,
    mut v_inst_5786_: *mut crate::leanh::LeanObject,
    mut v_inst_5787_: *mut crate::leanh::LeanObject,
    mut v_x_5788_: *mut crate::leanh::LeanObject,
    mut v_stx_5789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5790_ = crate::leanh::lean_apply_1(v_x_5788_, v_stx_5789_);
    v___x_5791_ = l_Lean_Elab_liftMacroM___redArg(
        v_inst_5778_,
        v_inst_5779_,
        v_inst_5780_,
        v_inst_5781_,
        v_inst_5782_,
        v_inst_5783_,
        v_inst_5784_,
        v_inst_5785_,
        v_inst_5786_,
        v___x_5790_,
    );
    return v___x_5791_;
}
pub unsafe fn l_Lean_Elab_adaptMacro___boxed(
    mut v_m_5792_: *mut crate::leanh::LeanObject,
    mut v_inst_5793_: *mut crate::leanh::LeanObject,
    mut v_inst_5794_: *mut crate::leanh::LeanObject,
    mut v_inst_5795_: *mut crate::leanh::LeanObject,
    mut v_inst_5796_: *mut crate::leanh::LeanObject,
    mut v_inst_5797_: *mut crate::leanh::LeanObject,
    mut v_inst_5798_: *mut crate::leanh::LeanObject,
    mut v_inst_5799_: *mut crate::leanh::LeanObject,
    mut v_inst_5800_: *mut crate::leanh::LeanObject,
    mut v_inst_5801_: *mut crate::leanh::LeanObject,
    mut v_inst_5802_: *mut crate::leanh::LeanObject,
    mut v_x_5803_: *mut crate::leanh::LeanObject,
    mut v_stx_5804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5805_ = l_Lean_Elab_adaptMacro(
        v_m_5792_,
        v_inst_5793_,
        v_inst_5794_,
        v_inst_5795_,
        v_inst_5796_,
        v_inst_5797_,
        v_inst_5798_,
        v_inst_5799_,
        v_inst_5800_,
        v_inst_5801_,
        v_inst_5802_,
        v_x_5803_,
        v_stx_5804_,
    );
    crate::leanh::lean_dec(v_inst_5802_);
    return v_res_5805_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(
    mut v_baseName_5806_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5807_: *mut crate::leanh::LeanObject,
    mut v_idx_5808_: *mut crate::leanh::LeanObject,
    mut v_a_5809_: *mut crate::leanh::LeanObject,
    mut v_a_5810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: u8 = 0;
    let mut v_a_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5823_: u8 = 0;
    let mut v_unused_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5833_: u8 = 0;
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_idx_5808_);
                crate::leanh::lean_inc(v_baseName_5806_);
                v_name_5811_ = lean_name_append_index_after(v_baseName_5806_, v_idx_5808_);
                crate::leanh::lean_inc(v_name_5811_);
                crate::leanh::lean_inc(v_currNamespace_5807_);
                v___x_5812_ = l_Lean_Name_append(v_currNamespace_5807_, v_name_5811_);
                v___x_5813_ = l_Lean_Macro_hasDecl(v___x_5812_, v_a_5809_, v_a_5810_);
                if crate::leanh::lean_obj_tag(v___x_5813_) == 0 {
                    v_a_5814_ = crate::leanh::lean_ctor_get(v___x_5813_, 0);
                    crate::leanh::lean_inc(v_a_5814_);
                    v___x_5815_ = (crate::leanh::lean_unbox(v_a_5814_) as u8);
                    crate::leanh::lean_dec(v_a_5814_);
                    if v___x_5815_ == 0 {
                        crate::leanh::lean_dec(v_idx_5808_);
                        crate::leanh::lean_dec(v_currNamespace_5807_);
                        crate::leanh::lean_dec(v_baseName_5806_);
                        v_a_5816_ = crate::leanh::lean_ctor_get(v___x_5813_, 1);
                        v_isSharedCheck_5823_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5813_)) as u8;
                        if v_isSharedCheck_5823_ == 0 {
                            v_unused_5824_ = crate::leanh::lean_ctor_get(v___x_5813_, 0);
                            crate::leanh::lean_dec(v_unused_5824_);
                            v___x_5818_ = v___x_5813_;
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5816_);
                            crate::leanh::lean_dec(v___x_5813_);
                            v___x_5818_ = crate::leanh::lean_box(0);
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_name_5811_);
                        v_a_5825_ = crate::leanh::lean_ctor_get(v___x_5813_, 1);
                        crate::leanh::lean_inc(v_a_5825_);
                        crate::leanh::lean_dec_ref_known(v___x_5813_, 2);
                        v___x_5826_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5827_ = lean_nat_add(v_idx_5808_, v___x_5826_);
                        crate::leanh::lean_dec(v_idx_5808_);
                        v_idx_5808_ = v___x_5827_;
                        v_a_5810_ = v_a_5825_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_5811_);
                    crate::leanh::lean_dec(v_idx_5808_);
                    crate::leanh::lean_dec(v_currNamespace_5807_);
                    crate::leanh::lean_dec(v_baseName_5806_);
                    v_a_5829_ = crate::leanh::lean_ctor_get(v___x_5813_, 0);
                    v_a_5830_ = crate::leanh::lean_ctor_get(v___x_5813_, 1);
                    v_isSharedCheck_5837_ = (!crate::leanh::lean_is_exclusive(v___x_5813_)) as u8;
                    if v_isSharedCheck_5837_ == 0 {
                        v___x_5832_ = v___x_5813_;
                        v_isShared_5833_ = v_isSharedCheck_5837_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5830_);
                        crate::leanh::lean_inc(v_a_5829_);
                        crate::leanh::lean_dec(v___x_5813_);
                        v___x_5832_ = crate::leanh::lean_box(0);
                        v_isShared_5833_ = v_isSharedCheck_5837_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5819_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5818_, 0, v_name_5811_);
                    v___x_5821_ = v___x_5818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5822_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_name_5811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5822_, 1, v_a_5816_);
                    v___x_5821_ = v_reuseFailAlloc_5822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5821_;
            }
            3 => {
                if v_isShared_5833_ == 0 {
                    v___x_5835_ = v___x_5832_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5836_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_a_5829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5836_, 1, v_a_5830_);
                    v___x_5835_ = v_reuseFailAlloc_5836_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop___boxed(
    mut v_baseName_5838_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5839_: *mut crate::leanh::LeanObject,
    mut v_idx_5840_: *mut crate::leanh::LeanObject,
    mut v_a_5841_: *mut crate::leanh::LeanObject,
    mut v_a_5842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5843_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(
        v_baseName_5838_,
        v_currNamespace_5839_,
        v_idx_5840_,
        v_a_5841_,
        v_a_5842_,
    );
    crate::leanh::lean_dec_ref(v_a_5841_);
    return v_res_5843_;
}
pub unsafe fn l_Lean_Elab_mkUnusedBaseName(
    mut v_baseName_5844_: *mut crate::leanh::LeanObject,
    mut v_a_5845_: *mut crate::leanh::LeanObject,
    mut v_a_5846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: u8 = 0;
    let mut v_a_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5857_: u8 = 0;
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5861_: u8 = 0;
    let mut v_unused_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5870_: u8 = 0;
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5847_ = l_Lean_Macro_getCurrNamespace(v_a_5845_, v_a_5846_);
                if crate::leanh::lean_obj_tag(v___x_5847_) == 0 {
                    v_a_5848_ = crate::leanh::lean_ctor_get(v___x_5847_, 0);
                    crate::leanh::lean_inc_n(v_a_5848_, 2);
                    v_a_5849_ = crate::leanh::lean_ctor_get(v___x_5847_, 1);
                    crate::leanh::lean_inc(v_a_5849_);
                    crate::leanh::lean_dec_ref_known(v___x_5847_, 2);
                    crate::leanh::lean_inc(v_baseName_5844_);
                    v___x_5850_ = l_Lean_Name_append(v_a_5848_, v_baseName_5844_);
                    v___x_5851_ = l_Lean_Macro_hasDecl(v___x_5850_, v_a_5845_, v_a_5849_);
                    if crate::leanh::lean_obj_tag(v___x_5851_) == 0 {
                        v_a_5852_ = crate::leanh::lean_ctor_get(v___x_5851_, 0);
                        crate::leanh::lean_inc(v_a_5852_);
                        v___x_5853_ = (crate::leanh::lean_unbox(v_a_5852_) as u8);
                        crate::leanh::lean_dec(v_a_5852_);
                        if v___x_5853_ == 0 {
                            crate::leanh::lean_dec(v_a_5848_);
                            v_a_5854_ = crate::leanh::lean_ctor_get(v___x_5851_, 1);
                            v_isSharedCheck_5861_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5851_)) as u8;
                            if v_isSharedCheck_5861_ == 0 {
                                v_unused_5862_ = crate::leanh::lean_ctor_get(v___x_5851_, 0);
                                crate::leanh::lean_dec(v_unused_5862_);
                                v___x_5856_ = v___x_5851_;
                                v_isShared_5857_ = v_isSharedCheck_5861_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5854_);
                                crate::leanh::lean_dec(v___x_5851_);
                                v___x_5856_ = crate::leanh::lean_box(0);
                                v_isShared_5857_ = v_isSharedCheck_5861_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_5863_ = crate::leanh::lean_ctor_get(v___x_5851_, 1);
                            crate::leanh::lean_inc(v_a_5863_);
                            crate::leanh::lean_dec_ref_known(v___x_5851_, 2);
                            v___x_5864_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_5865_ =
                                l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(
                                    v_baseName_5844_,
                                    v_a_5848_,
                                    v___x_5864_,
                                    v_a_5845_,
                                    v_a_5863_,
                                );
                            return v___x_5865_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5848_);
                        crate::leanh::lean_dec(v_baseName_5844_);
                        v_a_5866_ = crate::leanh::lean_ctor_get(v___x_5851_, 0);
                        v_a_5867_ = crate::leanh::lean_ctor_get(v___x_5851_, 1);
                        v_isSharedCheck_5874_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5851_)) as u8;
                        if v_isSharedCheck_5874_ == 0 {
                            v___x_5869_ = v___x_5851_;
                            v_isShared_5870_ = v_isSharedCheck_5874_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5867_);
                            crate::leanh::lean_inc(v_a_5866_);
                            crate::leanh::lean_dec(v___x_5851_);
                            v___x_5869_ = crate::leanh::lean_box(0);
                            v_isShared_5870_ = v_isSharedCheck_5874_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_baseName_5844_);
                    return v___x_5847_;
                }
            }
            1 => {
                if v_isShared_5857_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5856_, 0, v_baseName_5844_);
                    v___x_5859_ = v___x_5856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5860_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_baseName_5844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5860_, 1, v_a_5854_);
                    v___x_5859_ = v_reuseFailAlloc_5860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5859_;
            }
            3 => {
                if v_isShared_5870_ == 0 {
                    v___x_5872_ = v___x_5869_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5873_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5873_, 1, v_a_5867_);
                    v___x_5872_ = v_reuseFailAlloc_5873_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_mkUnusedBaseName___boxed(
    mut v_baseName_5875_: *mut crate::leanh::LeanObject,
    mut v_a_5876_: *mut crate::leanh::LeanObject,
    mut v_a_5877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5878_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_5875_, v_a_5876_, v_a_5877_);
    crate::leanh::lean_dec_ref(v_a_5876_);
    return v_res_5878_;
}
pub unsafe fn _init_l_Lean_Elab_logException___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5880_ = l_Lean_Elab_logException___redArg___lam__0___closed__0;
    v___x_5881_ = l_Lean_stringToMessageData(v___x_5880_);
    return v___x_5881_;
}
pub unsafe fn l_Lean_Elab_logException___redArg___lam__0(
    mut v_inst_5882_: *mut crate::leanh::LeanObject,
    mut v_inst_5883_: *mut crate::leanh::LeanObject,
    mut v_inst_5884_: *mut crate::leanh::LeanObject,
    mut v_inst_5885_: *mut crate::leanh::LeanObject,
    mut v_name_5886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5887_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_logException___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_logException___redArg___lam__0___closed__1_once),
        _init_l_Lean_Elab_logException___redArg___lam__0___closed__1,
    );
    v___x_5888_ = l_Lean_MessageData_ofName(v_name_5886_);
    v___x_5889_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5889_, 0, v___x_5887_);
    crate::leanh::lean_ctor_set(v___x_5889_, 1, v___x_5888_);
    v___x_5890_ = l_Lean_logError___redArg(
        v_inst_5882_,
        v_inst_5883_,
        v_inst_5884_,
        v_inst_5885_,
        v___x_5889_,
    );
    return v___x_5890_;
}
pub unsafe fn l_Lean_Elab_logException___redArg(
    mut v_inst_5891_: *mut crate::leanh::LeanObject,
    mut v_inst_5892_: *mut crate::leanh::LeanObject,
    mut v_inst_5893_: *mut crate::leanh::LeanObject,
    mut v_inst_5894_: *mut crate::leanh::LeanObject,
    mut v_inst_5895_: *mut crate::leanh::LeanObject,
    mut v_ex_5896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5903_: u8 = 0;
    let mut v_toBind_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: u8 = 0;
    let mut v___x_5913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_ex_5896_) == 0 {
                    crate::leanh::lean_dec(v_inst_5895_);
                    v_ref_5897_ = crate::leanh::lean_ctor_get(v_ex_5896_, 0);
                    crate::leanh::lean_inc(v_ref_5897_);
                    v_msg_5898_ = crate::leanh::lean_ctor_get(v_ex_5896_, 1);
                    crate::leanh::lean_inc_ref(v_msg_5898_);
                    crate::leanh::lean_dec_ref_known(v_ex_5896_, 2);
                    v___x_5899_ = l_Lean_logErrorAt___redArg(
                        v_inst_5891_,
                        v_inst_5892_,
                        v_inst_5893_,
                        v_inst_5894_,
                        v_ref_5897_,
                        v_msg_5898_,
                    );
                    return v___x_5899_;
                } else {
                    v_id_5900_ = crate::leanh::lean_ctor_get(v_ex_5896_, 0);
                    crate::leanh::lean_inc(v_id_5900_);
                    crate::leanh::lean_inc_ref(v_inst_5891_);
                    v___f_5901_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_logException___redArg___lam__0 as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_5901_, 0, v_inst_5891_);
                    crate::leanh::lean_closure_set(v___f_5901_, 1, v_inst_5892_);
                    crate::leanh::lean_closure_set(v___f_5901_, 2, v_inst_5893_);
                    crate::leanh::lean_closure_set(v___f_5901_, 3, v_inst_5894_);
                    v___x_5912_ = l_Lean_Elab_isAbortExceptionId(v_id_5900_);
                    if v___x_5912_ == 0 {
                        v___x_5913_ = l_Lean_Exception_isInterrupt(v_ex_5896_);
                        crate::leanh::lean_dec_ref_known(v_ex_5896_, 2);
                        v___y_5903_ = v___x_5913_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_ex_5896_, 2);
                        v___y_5903_ = v___x_5912_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5903_ == 0 {
                    v_toBind_5904_ = crate::leanh::lean_ctor_get(v_inst_5891_, 1);
                    crate::leanh::lean_inc(v_toBind_5904_);
                    crate::leanh::lean_dec_ref(v_inst_5891_);
                    v___x_5905_ = crate::leanh::lean_alloc_closure(
                        l_Lean_InternalExceptionId_getName___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_5905_, 0, v_id_5900_);
                    v___x_5906_ = crate::leanh::lean_apply_2(
                        v_inst_5895_,
                        crate::leanh::lean_box(0),
                        v___x_5905_,
                    );
                    v___x_5907_ = crate::leanh::lean_apply_4(
                        v_toBind_5904_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_5906_,
                        v___f_5901_,
                    );
                    return v___x_5907_;
                } else {
                    crate::leanh::lean_dec_ref(v___f_5901_);
                    crate::leanh::lean_dec(v_id_5900_);
                    crate::leanh::lean_dec(v_inst_5895_);
                    v_toApplicative_5908_ = crate::leanh::lean_ctor_get(v_inst_5891_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_5908_);
                    crate::leanh::lean_dec_ref(v_inst_5891_);
                    v_toPure_5909_ = crate::leanh::lean_ctor_get(v_toApplicative_5908_, 1);
                    crate::leanh::lean_inc(v_toPure_5909_);
                    crate::leanh::lean_dec_ref(v_toApplicative_5908_);
                    v___x_5910_ = crate::leanh::lean_box(0);
                    v___x_5911_ = crate::leanh::lean_apply_2(
                        v_toPure_5909_,
                        crate::leanh::lean_box(0),
                        v___x_5910_,
                    );
                    return v___x_5911_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_logException(
    mut v_m_5914_: *mut crate::leanh::LeanObject,
    mut v_inst_5915_: *mut crate::leanh::LeanObject,
    mut v_inst_5916_: *mut crate::leanh::LeanObject,
    mut v_inst_5917_: *mut crate::leanh::LeanObject,
    mut v_inst_5918_: *mut crate::leanh::LeanObject,
    mut v_inst_5919_: *mut crate::leanh::LeanObject,
    mut v_ex_5920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5921_ = l_Lean_Elab_logException___redArg(
        v_inst_5915_,
        v_inst_5916_,
        v_inst_5917_,
        v_inst_5918_,
        v_inst_5919_,
        v_ex_5920_,
    );
    return v___x_5921_;
}
pub unsafe fn l_Lean_Elab_withLogging___redArg___lam__0(
    mut v_inst_5922_: *mut crate::leanh::LeanObject,
    mut v_inst_5923_: *mut crate::leanh::LeanObject,
    mut v_inst_5924_: *mut crate::leanh::LeanObject,
    mut v_inst_5925_: *mut crate::leanh::LeanObject,
    mut v_inst_5926_: *mut crate::leanh::LeanObject,
    mut v_ex_5927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5928_ = l_Lean_Elab_logException___redArg(
        v_inst_5922_,
        v_inst_5923_,
        v_inst_5924_,
        v_inst_5925_,
        v_inst_5926_,
        v_ex_5927_,
    );
    return v___x_5928_;
}
pub unsafe fn l_Lean_Elab_withLogging___redArg(
    mut v_inst_5929_: *mut crate::leanh::LeanObject,
    mut v_inst_5930_: *mut crate::leanh::LeanObject,
    mut v_inst_5931_: *mut crate::leanh::LeanObject,
    mut v_inst_5932_: *mut crate::leanh::LeanObject,
    mut v_inst_5933_: *mut crate::leanh::LeanObject,
    mut v_inst_5934_: *mut crate::leanh::LeanObject,
    mut v_x_5935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_5936_ = crate::leanh::lean_ctor_get(v_inst_5931_, 1);
    crate::leanh::lean_inc(v_tryCatch_5936_);
    crate::leanh::lean_dec_ref(v_inst_5931_);
    v___f_5937_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_withLogging___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_5937_, 0, v_inst_5929_);
    crate::leanh::lean_closure_set(v___f_5937_, 1, v_inst_5930_);
    crate::leanh::lean_closure_set(v___f_5937_, 2, v_inst_5932_);
    crate::leanh::lean_closure_set(v___f_5937_, 3, v_inst_5933_);
    crate::leanh::lean_closure_set(v___f_5937_, 4, v_inst_5934_);
    v___x_5938_ = crate::leanh::lean_apply_3(
        v_tryCatch_5936_,
        crate::leanh::lean_box(0),
        v_x_5935_,
        v___f_5937_,
    );
    return v___x_5938_;
}
pub unsafe fn l_Lean_Elab_withLogging(
    mut v_m_5939_: *mut crate::leanh::LeanObject,
    mut v_inst_5940_: *mut crate::leanh::LeanObject,
    mut v_inst_5941_: *mut crate::leanh::LeanObject,
    mut v_inst_5942_: *mut crate::leanh::LeanObject,
    mut v_inst_5943_: *mut crate::leanh::LeanObject,
    mut v_inst_5944_: *mut crate::leanh::LeanObject,
    mut v_inst_5945_: *mut crate::leanh::LeanObject,
    mut v_x_5946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5947_ = l_Lean_Elab_withLogging___redArg(
        v_inst_5940_,
        v_inst_5941_,
        v_inst_5942_,
        v_inst_5943_,
        v_inst_5944_,
        v_inst_5945_,
        v_x_5946_,
    );
    return v___x_5947_;
}
pub unsafe fn _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5949_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0;
    v___x_5950_ = l_Lean_stringToMessageData(v___x_5949_);
    return v___x_5950_;
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(
    mut v_val_5951_: *mut crate::leanh::LeanObject,
    mut v_ex_5952_: *mut crate::leanh::LeanObject,
    mut v_toPure_5953_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exPosition_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5960_: u8 = 0;
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exPosition_5955_ = l_Lean_FileMap_toPosition(v_____do__lift_5954_, v_val_5951_);
                v_line_5956_ = crate::leanh::lean_ctor_get(v_exPosition_5955_, 0);
                v_column_5957_ = crate::leanh::lean_ctor_get(v_exPosition_5955_, 1);
                v_isSharedCheck_5977_ =
                    (!crate::leanh::lean_is_exclusive(v_exPosition_5955_)) as u8;
                if v_isSharedCheck_5977_ == 0 {
                    v___x_5959_ = v_exPosition_5955_;
                    v_isShared_5960_ = v_isSharedCheck_5977_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_column_5957_);
                    crate::leanh::lean_inc(v_line_5956_);
                    crate::leanh::lean_dec(v_exPosition_5955_);
                    v___x_5959_ = crate::leanh::lean_box(0);
                    v_isShared_5960_ = v_isSharedCheck_5977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5961_ = l_Nat_reprFast(v_line_5956_);
                v___x_5962_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5962_, 0, v___x_5961_);
                v___x_5963_ = l_Lean_MessageData_ofFormat(v___x_5962_);
                v___x_5964_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1,
                );
                if v_isShared_5960_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5959_, 7);
                    crate::leanh::lean_ctor_set(v___x_5959_, 1, v___x_5964_);
                    crate::leanh::lean_ctor_set(v___x_5959_, 0, v___x_5963_);
                    v___x_5966_ = v___x_5959_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5976_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5976_, 0, v___x_5963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5976_, 1, v___x_5964_);
                    v___x_5966_ = v_reuseFailAlloc_5976_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5967_ = l_Nat_reprFast(v_column_5957_);
                v___x_5968_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5968_, 0, v___x_5967_);
                v___x_5969_ = l_Lean_MessageData_ofFormat(v___x_5968_);
                v___x_5970_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5970_, 0, v___x_5966_);
                crate::leanh::lean_ctor_set(v___x_5970_, 1, v___x_5969_);
                v___x_5971_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
                v___x_5972_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5972_, 0, v___x_5970_);
                crate::leanh::lean_ctor_set(v___x_5972_, 1, v___x_5971_);
                v___x_5973_ = l_Lean_Exception_toMessageData(v_ex_5952_);
                v___x_5974_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5974_, 0, v___x_5972_);
                crate::leanh::lean_ctor_set(v___x_5974_, 1, v___x_5973_);
                v___x_5975_ = crate::leanh::lean_apply_2(
                    v_toPure_5953_,
                    crate::leanh::lean_box(0),
                    v___x_5974_,
                );
                return v___x_5975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(
    mut v_val_5978_: *mut crate::leanh::LeanObject,
    mut v_ex_5979_: *mut crate::leanh::LeanObject,
    mut v_toPure_5980_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5982_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(
        v_val_5978_,
        v_ex_5979_,
        v_toPure_5980_,
        v_____do__lift_5981_,
    );
    crate::leanh::lean_dec(v_val_5978_);
    return v_res_5982_;
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(
    mut v_ex_5983_: *mut crate::leanh::LeanObject,
    mut v_toPure_5984_: *mut crate::leanh::LeanObject,
    mut v_inst_5985_: *mut crate::leanh::LeanObject,
    mut v_toBind_5986_: *mut crate::leanh::LeanObject,
    mut v_pos_5987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: u8 = 0;
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5988_ = l_Lean_Exception_getRef(v_ex_5983_);
    v___x_5989_ = 0;
    v___x_5990_ = l_Lean_Syntax_getPos_x3f(v___x_5988_, v___x_5989_);
    crate::leanh::lean_dec(v___x_5988_);
    if crate::leanh::lean_obj_tag(v___x_5990_) == 0 {
        let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_5986_);
        crate::leanh::lean_dec_ref(v_inst_5985_);
        v___x_5991_ = l_Lean_Exception_toMessageData(v_ex_5983_);
        v___x_5992_ =
            crate::leanh::lean_apply_2(v_toPure_5984_, crate::leanh::lean_box(0), v___x_5991_);
        return v___x_5992_;
    } else {
        let mut v_val_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5994_: u8 = 0;
        v_val_5993_ = crate::leanh::lean_ctor_get(v___x_5990_, 0);
        crate::leanh::lean_inc(v_val_5993_);
        crate::leanh::lean_dec_ref_known(v___x_5990_, 1);
        v___x_5994_ = lean_nat_dec_eq(v_pos_5987_, v_val_5993_);
        if v___x_5994_ == 0 {
            let mut v_toMonadFileMap_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toMonadFileMap_5995_ = crate::leanh::lean_ctor_get(v_inst_5985_, 0);
            crate::leanh::lean_inc(v_toMonadFileMap_5995_);
            crate::leanh::lean_dec_ref(v_inst_5985_);
            v___f_5996_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_5996_, 0, v_val_5993_);
            crate::leanh::lean_closure_set(v___f_5996_, 1, v_ex_5983_);
            crate::leanh::lean_closure_set(v___f_5996_, 2, v_toPure_5984_);
            v___x_5997_ = crate::leanh::lean_apply_4(
                v_toBind_5986_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_toMonadFileMap_5995_,
                v___f_5996_,
            );
            return v___x_5997_;
        } else {
            let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_5993_);
            crate::leanh::lean_dec(v_toBind_5986_);
            crate::leanh::lean_dec_ref(v_inst_5985_);
            v___x_5998_ = l_Lean_Exception_toMessageData(v_ex_5983_);
            v___x_5999_ =
                crate::leanh::lean_apply_2(v_toPure_5984_, crate::leanh::lean_box(0), v___x_5998_);
            return v___x_5999_;
        }
    }
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(
    mut v_ex_6000_: *mut crate::leanh::LeanObject,
    mut v_toPure_6001_: *mut crate::leanh::LeanObject,
    mut v_inst_6002_: *mut crate::leanh::LeanObject,
    mut v_toBind_6003_: *mut crate::leanh::LeanObject,
    mut v_pos_6004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6005_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(
        v_ex_6000_,
        v_toPure_6001_,
        v_inst_6002_,
        v_toBind_6003_,
        v_pos_6004_,
    );
    crate::leanh::lean_dec(v_pos_6004_);
    return v_res_6005_;
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg(
    mut v_inst_6006_: *mut crate::leanh::LeanObject,
    mut v_inst_6007_: *mut crate::leanh::LeanObject,
    mut v_ex_6008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6009_ = crate::leanh::lean_ctor_get(v_inst_6006_, 0);
    v_toBind_6010_ = crate::leanh::lean_ctor_get(v_inst_6006_, 1);
    crate::leanh::lean_inc_n(v_toBind_6010_, 2);
    v_toPure_6011_ = crate::leanh::lean_ctor_get(v_toApplicative_6009_, 1);
    crate::leanh::lean_inc(v_toPure_6011_);
    crate::leanh::lean_inc_ref(v_inst_6007_);
    v___x_6012_ = l_Lean_getRefPos___redArg(v_inst_6006_, v_inst_6007_);
    v___f_6013_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6013_, 0, v_ex_6008_);
    crate::leanh::lean_closure_set(v___f_6013_, 1, v_toPure_6011_);
    crate::leanh::lean_closure_set(v___f_6013_, 2, v_inst_6007_);
    crate::leanh::lean_closure_set(v___f_6013_, 3, v_toBind_6010_);
    v___x_6014_ = crate::leanh::lean_apply_4(
        v_toBind_6010_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6012_,
        v___f_6013_,
    );
    return v___x_6014_;
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData(
    mut v_m_6015_: *mut crate::leanh::LeanObject,
    mut v_inst_6016_: *mut crate::leanh::LeanObject,
    mut v_inst_6017_: *mut crate::leanh::LeanObject,
    mut v_ex_6018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6019_ =
        l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_6016_, v_inst_6017_, v_ex_6018_);
    return v___x_6019_;
}
pub unsafe fn l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(
    mut v_inst_6020_: *mut crate::leanh::LeanObject,
    mut v_inst_6021_: *mut crate::leanh::LeanObject,
    mut v_x_6022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6023_ =
        l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_6020_, v_inst_6021_, v_x_6022_);
    return v___x_6023_;
}
pub unsafe fn _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6025_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0;
    v___x_6026_ = l_Lean_stringToMessageData(v___x_6025_);
    return v___x_6026_;
}
pub unsafe fn l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(
    mut v_msg_6027_: *mut crate::leanh::LeanObject,
    mut v_inst_6028_: *mut crate::leanh::LeanObject,
    mut v_inst_6029_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6031_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1,
    );
    v___x_6032_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6032_, 0, v_msg_6027_);
    crate::leanh::lean_ctor_set(v___x_6032_, 1, v___x_6031_);
    v___x_6033_ = l_Lean_toMessageList(v_____do__lift_6030_);
    v___x_6034_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6034_, 0, v___x_6032_);
    crate::leanh::lean_ctor_set(v___x_6034_, 1, v___x_6033_);
    v___x_6035_ = l_Lean_throwError___redArg(v_inst_6028_, v_inst_6029_, v___x_6034_);
    return v___x_6035_;
}
pub unsafe fn l_Lean_Elab_throwErrorWithNestedErrors___redArg(
    mut v_inst_6036_: *mut crate::leanh::LeanObject,
    mut v_inst_6037_: *mut crate::leanh::LeanObject,
    mut v_inst_6038_: *mut crate::leanh::LeanObject,
    mut v_msg_6039_: *mut crate::leanh::LeanObject,
    mut v_exs_6040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6044_: usize = 0;
    let mut v___x_6045_: usize = 0;
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6041_ = crate::leanh::lean_ctor_get(v_inst_6037_, 1);
    crate::leanh::lean_inc(v_toBind_6041_);
    crate::leanh::lean_inc_ref_n(v_inst_6037_, 2);
    v___f_6042_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6042_, 0, v_inst_6037_);
    crate::leanh::lean_closure_set(v___f_6042_, 1, v_inst_6038_);
    v___f_6043_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6043_, 0, v_msg_6039_);
    crate::leanh::lean_closure_set(v___f_6043_, 1, v_inst_6037_);
    crate::leanh::lean_closure_set(v___f_6043_, 2, v_inst_6036_);
    v_sz_6044_ = lean_array_size(v_exs_6040_);
    v___x_6045_ = 0usize;
    v___x_6046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_6037_,
        v___f_6042_,
        v_sz_6044_,
        v___x_6045_,
        v_exs_6040_,
    );
    v___x_6047_ = crate::leanh::lean_apply_4(
        v_toBind_6041_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6046_,
        v___f_6043_,
    );
    return v___x_6047_;
}
pub unsafe fn l_Lean_Elab_throwErrorWithNestedErrors(
    mut v_m_6048_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6049_: *mut crate::leanh::LeanObject,
    mut v_inst_6050_: *mut crate::leanh::LeanObject,
    mut v_inst_6051_: *mut crate::leanh::LeanObject,
    mut v_inst_6052_: *mut crate::leanh::LeanObject,
    mut v_msg_6053_: *mut crate::leanh::LeanObject,
    mut v_exs_6054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6055_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(
        v_inst_6050_,
        v_inst_6051_,
        v_inst_6052_,
        v_msg_6053_,
        v_exs_6054_,
    );
    return v___x_6055_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: u8 = 0;
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6122_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_;
    v___x_6123_ = 0;
    v___x_6124_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_;
    v___x_6125_ = l_Lean_registerTraceClass(v___x_6122_, v___x_6123_, v___x_6124_);
    if crate::leanh::lean_obj_tag(v___x_6125_) == 0 {
        let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_6125_, 1);
        v___x_6126_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_;
        v___x_6127_ = l_Lean_registerTraceClass(v___x_6126_, v___x_6123_, v___x_6124_);
        if crate::leanh::lean_obj_tag(v___x_6127_) == 0 {
            let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6129_: u8 = 0;
            let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_6127_, 1);
            v___x_6128_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_;
            v___x_6129_ = 1;
            v___x_6130_ = l_Lean_registerTraceClass(v___x_6128_, v___x_6129_, v___x_6124_);
            return v___x_6130_;
        } else {
            return v___x_6127_;
        }
    } else {
        return v___x_6125_;
    }
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2____boxed(
    mut v_a_6131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6132_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
    return v_res_6132_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Extension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_KeyedDeclsAttribute(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_BuiltinDocAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_pp_macroStack = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_pp_macroStack);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_macroAttribute = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_macroAttribute);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_mkElabAttribute___auto__1 = _init_l_Lean_Elab_mkElabAttribute___auto__1();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_mkElabAttribute___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Extension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_KeyedDeclsAttribute(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_BuiltinDocAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Util(builtin);
}
