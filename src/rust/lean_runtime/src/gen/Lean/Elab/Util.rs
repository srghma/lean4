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
    l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_mkAtom, l_Lean_replaceRef, l_List_foldl___at___00Lean_MacroScopesView_review_spec__0,
    l_List_foldl___redArg, l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
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
    initialize_Lean_Parser_Command, meta_initialize_Lean_Parser_Command,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_string_dec_eq, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Elab_expandOptNamedPrio___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_expandOptNamedPrio___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_expandOptNamedPrio___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_expandOptNamedPrio___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_expandOptNamedPrio___closed__2_value: LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_expandOptNamedPrio___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_expandOptNamedPrio___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_expandOptNamedPrio___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__3_value) as *mut LeanObject;
static l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__2_value) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_expandOptNamedPrio___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__4_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__3_value) as *mut LeanObject,
        13348752267415789739 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_expandOptNamedPrio___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 99, 114, 111, 83, 116, 97, 99, 107, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,1314940330429522239 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [100, 105, 115, 112, 108, 97, 121, 32, 109, 97, 99, 114, 111, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 32, 115, 116, 97, 99, 107, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,8636882522227397730 as *mut LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,9662849064889376504 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112,
            97, 110, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100,
            101, 32, 107, 105, 110, 100, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0_value
) as *mut LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__0_value) as *mut LeanObject,5337926038336999469 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__1_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__1_value) as *mut LeanObject;
static l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__1_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__3_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__4_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__4_value) as *mut LeanObject;
static l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__4_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__6_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__6_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__8_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__8_value) as *mut LeanObject;
static l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__8_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__9_value) as *mut LeanObject;
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__12_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__13_value: LeanStringObject<9> =
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
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__13_value)
        as *mut LeanObject;
static l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__12_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__13_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___auto__1___closed__15_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___auto__1___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_mkElabAttribute___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_mkElabAttribute___auto__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__6_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__13_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__23_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_mkElabAttribute___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_mkElabAttribute___redArg___closed__1_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkElabAttribute___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkElabAttribute___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__0_value)
                as *mut LeanObject,
            11704967964546086785 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__2_value)
                as *mut LeanObject,
            89168197957061509 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__4_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__4_value) as *mut LeanObject;
static l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__4_value)
                as *mut LeanObject,
            18105168627502861736 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_mkMacroAttributeUnsafe___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkMacroAttributeUnsafe___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [109, 97, 99, 114, 111, 65, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value) as *mut LeanObject,9634981646868643031 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0_value: LeanStringObject<391> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 391, m_capacity: 391, m_length: 388, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 32, 109, 97, 99, 114, 111, 32, 101, 120, 112, 97, 110, 100, 101, 114, 32, 102, 111, 114, 32, 97, 32, 103, 105, 118, 101, 110, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 46, 10, 10, 65, 32, 109, 97, 99, 114, 111, 32, 101, 120, 112, 97, 110, 100, 101, 114, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 32, 96, 76, 101, 97, 110, 46, 77, 97, 99, 114, 111, 96, 32, 40, 119, 104, 105, 99, 104, 32, 105, 115, 32, 96, 76, 101, 97, 110, 46, 83, 121, 110, 116, 97, 120, 32, 226, 134, 146, 32, 76, 101, 97, 110, 46, 77, 97, 99, 114, 111, 77, 32, 76, 101, 97, 110, 46, 83, 121, 110, 116, 97, 120, 96, 41, 44, 10, 105, 46, 101, 46, 32, 115, 104, 111, 117, 108, 100, 32, 116, 97, 107, 101, 32, 115, 121, 110, 116, 97, 120, 32, 111, 102, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 32, 97, 115, 32, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 97, 110, 100, 32, 112, 114, 111, 100, 117, 99, 101, 32, 100, 105, 102, 102, 101, 114, 101, 110, 116, 32, 115, 121, 110, 116, 97, 120, 10, 105, 110, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 115, 121, 110, 116, 97, 120, 32, 99, 97, 116, 101, 103, 111, 114, 121, 46, 10, 10, 84, 104, 101, 32, 96, 109, 97, 99, 114, 111, 95, 114, 117, 108, 101, 115, 96, 32, 97, 110, 100, 32, 96, 109, 97, 99, 114, 111, 96, 32, 99, 111, 109, 109, 97, 110, 100, 115, 32, 115, 104, 111, 117, 108, 100, 32, 117, 115, 117, 97, 108, 108, 121, 32, 98, 101, 32, 112, 114, 101, 102, 101, 114, 114, 101, 100, 32, 111, 118, 101, 114, 32, 117, 115, 105, 110, 103, 32, 116, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 10, 100, 105, 114, 101, 99, 116, 108, 121, 46, 10, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 139 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 150 as usize) << 1) | 1) as *mut LeanObject,((( 91 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__1_value) as *mut LeanObject,((( 91 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 150 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 150 as usize) << 1) | 1) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__4_value) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0_value: LeanStringObject<158> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 158,
        m_capacity: 158,
        m_length: 157,
        m_data: [
            109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32,
            100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99,
            104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111,
            110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62,
            96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105,
            116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32,
            100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32,
            116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32,
            105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_instMonad___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_instMonad___lam__2 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__3_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_map as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_liftMacroM___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__5_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_pure as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__6_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_seqRight as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__7_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_liftMacroM___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__8_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_bind as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_liftMacroM___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_liftMacroM___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__9_value) as *mut LeanObject;
static mut l_Lean_Elab_liftMacroM___redArg___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_liftMacroM___redArg___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_liftMacroM___redArg___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_liftMacroM___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_liftMacroM___redArg___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_liftMacroM___redArg___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_liftMacroM___redArg___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_liftMacroM___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_liftMacroM___redArg___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_liftMacroM___redArg___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___redArg___closed__15_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ReaderT_pure___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_liftMacroM___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_liftMacroM___redArg___closed__15_value) as *mut LeanObject;
pub static l_Lean_Elab_logException___redArg___lam__0___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110,
            58, 32, 0,
        ],
    };
static mut l_Lean_Elab_logException___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_logException___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_logException___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_logException___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,13803056972440293078 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,2082380159358162175 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut LeanObject,5163195698633565746 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,3797997157859537744 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,349153818491263805 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,8303187326548929696 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_expandOptNamedPrio___closed__0_value) as *mut LeanObject,4832156502452437593 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,11911250769714989207 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,1771634189876703749 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,((( 2034298159 as usize) << 1) | 1) as *mut LeanObject,18033771262542104897 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,5059639781667360386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,6203526536341765518 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,10631922230448659167 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 101, 112, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,16279398898093714393 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 115, 117, 108, 116, 0]};
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,16279398898093714393 as *mut LeanObject] };
pub static l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject,4251351871078927870 as *mut LeanObject] };
static mut l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Syntax_prettyPrint(mut v_stx_3067_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_stx_3067_);
    v___x_3068_ = l_Lean_Syntax_unsetTrailing(v_stx_3067_);
    v___x_3069_ = l_Lean_Syntax_reprint(v___x_3068_);
    if lean_obj_tag(v___x_3069_) == 0 {
        let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3071_: u8 = 0;
        let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
        v___x_3070_ = lean_box(0);
        v___x_3071_ = 0;
        v___x_3072_ = l_Lean_Syntax_formatStx(v_stx_3067_, v___x_3070_, v___x_3071_);
        return v___x_3072_;
    } else {
        let mut v_val_3073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_3067_);
        v_val_3073_ = lean_ctor_get(v___x_3069_, 0);
        lean_inc(v_val_3073_);
        lean_dec_ref_known(v___x_3069_, 1);
        v___x_3074_ = l_String_toFormat(v_val_3073_);
        return v___x_3074_;
    }
}
pub unsafe fn l_Lean_MacroScopesView_format(
    mut v_view_3075_: *mut LeanObject,
    mut v_mainModule_3076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: u8 = 0;
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3082_ = lean_ctor_get(v_view_3075_, 0);
                lean_inc(v_name_3082_);
                v_imported_3083_ = lean_ctor_get(v_view_3075_, 1);
                lean_inc(v_imported_3083_);
                v_ctx_3084_ = lean_ctor_get(v_view_3075_, 2);
                lean_inc(v_ctx_3084_);
                v_scopes_3085_ = lean_ctor_get(v_view_3075_, 3);
                lean_inc(v_scopes_3085_);
                lean_dec_ref(v_view_3075_);
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
                        lean_dec(v_ctx_3084_);
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
                    lean_dec(v_scopes_3085_);
                    lean_dec(v_ctx_3084_);
                    lean_dec(v_imported_3083_);
                    v___y_3078_ = v_name_3082_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3079_ = 1;
                v___x_3080_ = l_Lean_Name_toString(v___y_3078_, v___x_3079_);
                v___x_3081_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3081_, 0, v___x_3080_);
                return v___x_3081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MacroScopesView_format___boxed(
    mut v_view_3093_: *mut LeanObject,
    mut v_mainModule_3094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3095_: *mut LeanObject = core::ptr::null_mut();
    v_res_3095_ = l_Lean_MacroScopesView_format(v_view_3093_, v_mainModule_3094_);
    lean_dec(v_mainModule_3094_);
    return v_res_3095_;
}
pub unsafe fn l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(
    mut v_x_3096_: *mut LeanObject,
    mut v_x_3097_: *mut LeanObject,
) -> u8 {
    let mut v___x_3098_: u8 = 0;
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: u8 = 0;
    let mut v_head_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3096_) == 0 {
                    if lean_obj_tag(v_x_3097_) == 0 {
                        v___x_3098_ = 1;
                        return v___x_3098_;
                    } else {
                        v___x_3099_ = 0;
                        return v___x_3099_;
                    }
                } else {
                    if lean_obj_tag(v_x_3097_) == 0 {
                        v___x_3100_ = 0;
                        return v___x_3100_;
                    } else {
                        v_head_3101_ = lean_ctor_get(v_x_3096_, 0);
                        v_tail_3102_ = lean_ctor_get(v_x_3096_, 1);
                        v_head_3103_ = lean_ctor_get(v_x_3097_, 0);
                        v_tail_3104_ = lean_ctor_get(v_x_3097_, 1);
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
    mut v_x_3107_: *mut LeanObject,
    mut v_x_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3109_: u8 = 0;
    let mut v_r_3110_: *mut LeanObject = core::ptr::null_mut();
    v_res_3109_ = l_List_beq___at___00Lean_MacroScopesView_equalScope_spec__0(v_x_3107_, v_x_3108_);
    lean_dec(v_x_3108_);
    lean_dec(v_x_3107_);
    v_r_3110_ = lean_box((v_res_3109_) as usize);
    return v_r_3110_;
}
pub unsafe fn l_Lean_MacroScopesView_equalScope(
    mut v_a_3111_: *mut LeanObject,
    mut v_b_3112_: *mut LeanObject,
) -> u8 {
    let mut v_imported_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3120_: u8 = 0;
    let mut v___x_3121_: u8 = 0;
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imported_3113_ = lean_ctor_get(v_a_3111_, 1);
                v_ctx_3114_ = lean_ctor_get(v_a_3111_, 2);
                v_scopes_3115_ = lean_ctor_get(v_a_3111_, 3);
                v_imported_3116_ = lean_ctor_get(v_b_3112_, 1);
                v_ctx_3117_ = lean_ctor_get(v_b_3112_, 2);
                v_scopes_3118_ = lean_ctor_get(v_b_3112_, 3);
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
    mut v_a_3124_: *mut LeanObject,
    mut v_b_3125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3126_: u8 = 0;
    let mut v_r_3127_: *mut LeanObject = core::ptr::null_mut();
    v_res_3126_ = l_Lean_MacroScopesView_equalScope(v_a_3124_, v_b_3125_);
    lean_dec_ref(v_b_3125_);
    lean_dec_ref(v_a_3124_);
    v_r_3127_ = lean_box((v_res_3126_) as usize);
    return v_r_3127_;
}
pub unsafe fn l_Lean_Elab_expandOptNamedPrio(
    mut v_stx_3137_: *mut LeanObject,
    mut v_a_3138_: *mut LeanObject,
    mut v_a_3139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3140_: u8 = 0;
    v___x_3140_ = l_Lean_Syntax_isNone(v_stx_3137_);
    if v___x_3140_ == 0 {
        let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3144_: u8 = 0;
        v___x_3141_ = lean_unsigned_to_nat(0);
        v___x_3142_ = l_Lean_Syntax_getArg(v_stx_3137_, v___x_3141_);
        v___x_3143_ = l_Lean_Elab_expandOptNamedPrio___closed__4;
        lean_inc(v___x_3142_);
        v___x_3144_ = l_Lean_Syntax_isOfKind(v___x_3142_, v___x_3143_);
        if v___x_3144_ == 0 {
            let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_3142_);
            v___x_3145_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3139_);
            return v___x_3145_;
        } else {
            let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
            v___x_3146_ = lean_unsigned_to_nat(3);
            v___x_3147_ = l_Lean_Syntax_getArg(v___x_3142_, v___x_3146_);
            lean_dec(v___x_3142_);
            v___x_3148_ = l_Lean_evalPrio(v___x_3147_, v_a_3138_, v_a_3139_);
            return v___x_3148_;
        }
    } else {
        let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
        v___x_3149_ = lean_unsigned_to_nat(1000);
        v___x_3150_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3150_, 0, v___x_3149_);
        lean_ctor_set(v___x_3150_, 1, v_a_3139_);
        return v___x_3150_;
    }
}
pub unsafe fn l_Lean_Elab_expandOptNamedPrio___boxed(
    mut v_stx_3151_: *mut LeanObject,
    mut v_a_3152_: *mut LeanObject,
    mut v_a_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3154_: *mut LeanObject = core::ptr::null_mut();
    v_res_3154_ = l_Lean_Elab_expandOptNamedPrio(v_stx_3151_, v_a_3152_, v_a_3153_);
    lean_dec_ref(v_a_3152_);
    lean_dec(v_stx_3151_);
    return v_res_3154_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(
    mut v_x_3155_: *mut LeanObject,
    mut v_x_3156_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3155_) == 0 {
        if lean_obj_tag(v_x_3156_) == 0 {
            let mut v___x_3157_: u8 = 0;
            v___x_3157_ = 1;
            return v___x_3157_;
        } else {
            let mut v___x_3158_: u8 = 0;
            v___x_3158_ = 0;
            return v___x_3158_;
        }
    } else {
        if lean_obj_tag(v_x_3156_) == 0 {
            let mut v___x_3159_: u8 = 0;
            v___x_3159_ = 0;
            return v___x_3159_;
        } else {
            let mut v_val_3160_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_3161_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3162_: u8 = 0;
            v_val_3160_ = lean_ctor_get(v_x_3155_, 0);
            v_val_3161_ = lean_ctor_get(v_x_3156_, 0);
            v___x_3162_ = lean_nat_dec_eq(v_val_3160_, v_val_3161_);
            return v___x_3162_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0___boxed(
    mut v_x_3163_: *mut LeanObject,
    mut v_x_3164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3165_: u8 = 0;
    let mut v_r_3166_: *mut LeanObject = core::ptr::null_mut();
    v_res_3165_ =
        l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(v_x_3163_, v_x_3164_);
    lean_dec(v_x_3164_);
    lean_dec(v_x_3163_);
    v_r_3166_ = lean_box((v_res_3165_) as usize);
    return v_r_3166_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(
    mut v___x_3167_: *mut LeanObject,
    mut v_x_3168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_before_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3168_) == 0 {
                    v___x_3169_ = lean_box(0);
                    return v___x_3169_;
                } else {
                    v_head_3170_ = lean_ctor_get(v_x_3168_, 0);
                    v_tail_3171_ = lean_ctor_get(v_x_3168_, 1);
                    v_before_3172_ = lean_ctor_get(v_head_3170_, 0);
                    v___x_3173_ = 0;
                    v___x_3174_ = l_Lean_Syntax_getPos_x3f(v_before_3172_, v___x_3173_);
                    v___x_3175_ = l_Option_instBEq_beq___at___00Lean_Elab_getBetterRef_spec__0(
                        v___x_3174_,
                        v___x_3167_,
                    );
                    lean_dec(v___x_3174_);
                    if v___x_3175_ == 0 {
                        lean_inc(v_head_3170_);
                        v___x_3176_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3176_, 0, v_head_3170_);
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
    mut v___x_3178_: *mut LeanObject,
    mut v_x_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3180_: *mut LeanObject = core::ptr::null_mut();
    v_res_3180_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(v___x_3178_, v_x_3179_);
    lean_dec(v_x_3179_);
    lean_dec(v___x_3178_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_Elab_getBetterRef(
    mut v_ref_3181_: *mut LeanObject,
    mut v_macroStack_3182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3183_: u8 = 0;
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    v___x_3183_ = 0;
    v___x_3184_ = l_Lean_Syntax_getPos_x3f(v_ref_3181_, v___x_3183_);
    if lean_obj_tag(v___x_3184_) == 0 {
        let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
        v___x_3185_ = l_List_find_x3f___at___00Lean_Elab_getBetterRef_spec__1(
            v___x_3184_,
            v_macroStack_3182_,
        );
        if lean_obj_tag(v___x_3185_) == 0 {
            lean_inc(v_ref_3181_);
            return v_ref_3181_;
        } else {
            let mut v_val_3186_: *mut LeanObject = core::ptr::null_mut();
            let mut v_before_3187_: *mut LeanObject = core::ptr::null_mut();
            v_val_3186_ = lean_ctor_get(v___x_3185_, 0);
            lean_inc(v_val_3186_);
            lean_dec_ref_known(v___x_3185_, 1);
            v_before_3187_ = lean_ctor_get(v_val_3186_, 0);
            lean_inc(v_before_3187_);
            lean_dec(v_val_3186_);
            return v_before_3187_;
        }
    } else {
        lean_dec_ref_known(v___x_3184_, 1);
        lean_inc(v_ref_3181_);
        return v_ref_3181_;
    }
}
pub unsafe fn l_Lean_Elab_getBetterRef___boxed(
    mut v_ref_3188_: *mut LeanObject,
    mut v_macroStack_3189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3190_: *mut LeanObject = core::ptr::null_mut();
    v_res_3190_ = l_Lean_Elab_getBetterRef(v_ref_3188_, v_macroStack_3189_);
    lean_dec(v_macroStack_3189_);
    lean_dec(v_ref_3188_);
    return v_res_3190_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(
    mut v_name_3191_: *mut LeanObject,
    mut v_decl_3192_: *mut LeanObject,
    mut v_ref_3193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut v_unused_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3214_: u8 = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3195_ = lean_ctor_get(v_decl_3192_, 0);
                v_descr_3196_ = lean_ctor_get(v_decl_3192_, 1);
                v_deprecation_x3f_3197_ = lean_ctor_get(v_decl_3192_, 2);
                v___x_3198_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3199_ = (lean_unbox(v_defValue_3195_) as u8);
                lean_ctor_set_uint8(v___x_3198_, 0 as u32, v___x_3199_);
                lean_inc(v_deprecation_x3f_3197_);
                lean_inc_ref(v_descr_3196_);
                lean_inc_n(v_name_3191_, 2);
                v___x_3200_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3200_, 0, v_name_3191_);
                lean_ctor_set(v___x_3200_, 1, v_ref_3193_);
                lean_ctor_set(v___x_3200_, 2, v___x_3198_);
                lean_ctor_set(v___x_3200_, 3, v_descr_3196_);
                lean_ctor_set(v___x_3200_, 4, v_deprecation_x3f_3197_);
                v___x_3201_ = lean_register_option(v_name_3191_, v___x_3200_);
                if lean_obj_tag(v___x_3201_) == 0 {
                    v_isSharedCheck_3209_ = (!lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3209_ == 0 {
                        v_unused_3210_ = lean_ctor_get(v___x_3201_, 0);
                        lean_dec(v_unused_3210_);
                        v___x_3203_ = v___x_3201_;
                        v_isShared_3204_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3201_);
                        v___x_3203_ = lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_3191_);
                    v_a_3211_ = lean_ctor_get(v___x_3201_, 0);
                    v_isSharedCheck_3218_ = (!lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3218_ == 0 {
                        v___x_3213_ = v___x_3201_;
                        v_isShared_3214_ = v_isSharedCheck_3218_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3211_);
                        lean_dec(v___x_3201_);
                        v___x_3213_ = lean_box(0);
                        v_isShared_3214_ = v_isSharedCheck_3218_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_3195_);
                v___x_3205_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3205_, 0, v_name_3191_);
                lean_ctor_set(v___x_3205_, 1, v_defValue_3195_);
                if v_isShared_3204_ == 0 {
                    lean_ctor_set(v___x_3203_, 0, v___x_3205_);
                    v___x_3207_ = v___x_3203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3205_);
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
                    v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
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
    mut v_name_3219_: *mut LeanObject,
    mut v_decl_3220_: *mut LeanObject,
    mut v_ref_3221_: *mut LeanObject,
    mut v_a_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3223_: *mut LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v_name_3219_, v_decl_3220_, v_ref_3221_);
    lean_dec_ref(v_decl_3220_);
    return v_res_3223_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    v___x_3242_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_;
    v___x_3243_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_;
    v___x_3244_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_;
    v___x_3245_ = l_Lean_Option_register___at___00__private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4__spec__0(v___x_3242_, v___x_3243_, v___x_3244_);
    return v___x_3245_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4____boxed(
    mut v_a_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3247_: *mut LeanObject = core::ptr::null_mut();
    v_res_3247_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
    return v_res_3247_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Lean_Elab_addMacroStack___redArg___lam__0___closed__1;
    v___x_3252_ = l_Lean_MessageData_ofFormat(v___x_3251_);
    return v___x_3252_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___redArg___lam__0(
    mut v___x_3253_: *mut LeanObject,
    mut v_msgData_3254_: *mut LeanObject,
    mut v_elem_3255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_before_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut v_unused_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_before_3256_ = lean_ctor_get(v_elem_3255_, 0);
                v_isSharedCheck_3268_ = (!lean_is_exclusive(v_elem_3255_)) as u8;
                if v_isSharedCheck_3268_ == 0 {
                    v_unused_3269_ = lean_ctor_get(v_elem_3255_, 1);
                    lean_dec(v_unused_3269_);
                    v___x_3258_ = v_elem_3255_;
                    v_isShared_3259_ = v_isSharedCheck_3268_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_before_3256_);
                    lean_dec(v_elem_3255_);
                    v___x_3258_ = lean_box(0);
                    v_isShared_3259_ = v_isSharedCheck_3268_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3259_ == 0 {
                    lean_ctor_set_tag(v___x_3258_, 7);
                    lean_ctor_set(v___x_3258_, 1, v___x_3253_);
                    lean_ctor_set(v___x_3258_, 0, v_msgData_3254_);
                    v___x_3261_ = v___x_3258_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3267_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_msgData_3254_);
                    lean_ctor_set(v_reuseFailAlloc_3267_, 1, v___x_3253_);
                    v___x_3261_ = v_reuseFailAlloc_3267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3262_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2_once
                    ),
                    _init_l_Lean_Elab_addMacroStack___redArg___lam__0___closed__2,
                );
                v___x_3263_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3263_, 0, v___x_3261_);
                lean_ctor_set(v___x_3263_, 1, v___x_3262_);
                v___x_3264_ = l_Lean_MessageData_ofSyntax(v_before_3256_);
                v___x_3265_ = l_Lean_indentD(v___x_3264_);
                v___x_3266_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3266_, 0, v___x_3263_);
                lean_ctor_set(v___x_3266_, 1, v___x_3265_);
                return v___x_3266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0() -> *mut LeanObject {
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    v___x_3270_ = lean_box(1);
    v___x_3271_ = l_Lean_MessageData_ofFormat(v___x_3270_);
    return v___x_3271_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1() -> *mut LeanObject {
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3273_: *mut LeanObject = core::ptr::null_mut();
    v___x_3272_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once),
        _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0,
    );
    v___f_3273_ = lean_alloc_closure(
        l_Lean_Elab_addMacroStack___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3273_, 0, v___x_3272_);
    return v___f_3273_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4() -> *mut LeanObject {
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    v___x_3277_ = l_Lean_Elab_addMacroStack___redArg___lam__1___closed__3;
    v___x_3278_ = l_Lean_MessageData_ofFormat(v___x_3277_);
    return v___x_3278_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___redArg___lam__1(
    mut v___x_3279_: *mut LeanObject,
    mut v_toApplicative_3280_: *mut LeanObject,
    mut v_msgData_3281_: *mut LeanObject,
    mut v_macroStack_3282_: *mut LeanObject,
    mut v_____do__lift_3283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v_toPure_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v_toPure_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3309_: u8 = 0;
    let mut v_unused_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3284_ = l_Lean_Elab_pp_macroStack;
                v___x_3285_ =
                    l_Lean_Option_get___redArg(v___x_3279_, v_____do__lift_3283_, v___x_3284_);
                v___x_3286_ = (lean_unbox(v___x_3285_) as u8);
                lean_dec(v___x_3285_);
                if v___x_3286_ == 0 {
                    lean_dec(v_macroStack_3282_);
                    v_toPure_3287_ = lean_ctor_get(v_toApplicative_3280_, 1);
                    lean_inc(v_toPure_3287_);
                    lean_dec_ref(v_toApplicative_3280_);
                    v___x_3288_ = lean_apply_2(v_toPure_3287_, lean_box(0), v_msgData_3281_);
                    return v___x_3288_;
                } else {
                    if lean_obj_tag(v_macroStack_3282_) == 0 {
                        v_toPure_3289_ = lean_ctor_get(v_toApplicative_3280_, 1);
                        lean_inc(v_toPure_3289_);
                        lean_dec_ref(v_toApplicative_3280_);
                        v___x_3290_ = lean_apply_2(v_toPure_3289_, lean_box(0), v_msgData_3281_);
                        return v___x_3290_;
                    } else {
                        v_head_3291_ = lean_ctor_get(v_macroStack_3282_, 0);
                        lean_inc(v_head_3291_);
                        v_after_3292_ = lean_ctor_get(v_head_3291_, 1);
                        v_isSharedCheck_3309_ = (!lean_is_exclusive(v_head_3291_)) as u8;
                        if v_isSharedCheck_3309_ == 0 {
                            v_unused_3310_ = lean_ctor_get(v_head_3291_, 0);
                            lean_dec(v_unused_3310_);
                            v___x_3294_ = v_head_3291_;
                            v_isShared_3295_ = v_isSharedCheck_3309_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_3292_);
                            lean_dec(v_head_3291_);
                            v___x_3294_ = lean_box(0);
                            v_isShared_3295_ = v_isSharedCheck_3309_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_toPure_3296_ = lean_ctor_get(v_toApplicative_3280_, 1);
                lean_inc(v_toPure_3296_);
                lean_dec_ref(v_toApplicative_3280_);
                v___x_3297_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0_once
                    ),
                    _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__0,
                );
                v___f_3298_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1_once
                    ),
                    _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__1,
                );
                if v_isShared_3295_ == 0 {
                    lean_ctor_set_tag(v___x_3294_, 7);
                    lean_ctor_set(v___x_3294_, 1, v___x_3297_);
                    lean_ctor_set(v___x_3294_, 0, v_msgData_3281_);
                    v___x_3300_ = v___x_3294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3308_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_msgData_3281_);
                    lean_ctor_set(v_reuseFailAlloc_3308_, 1, v___x_3297_);
                    v___x_3300_ = v_reuseFailAlloc_3308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3301_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4_once
                    ),
                    _init_l_Lean_Elab_addMacroStack___redArg___lam__1___closed__4,
                );
                v___x_3302_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3302_, 0, v___x_3300_);
                lean_ctor_set(v___x_3302_, 1, v___x_3301_);
                v___x_3303_ = l_Lean_MessageData_ofSyntax(v_after_3292_);
                v___x_3304_ = l_Lean_indentD(v___x_3303_);
                v_msgData_3305_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_3305_, 0, v___x_3302_);
                lean_ctor_set(v_msgData_3305_, 1, v___x_3304_);
                v___x_3306_ =
                    l_List_foldl___redArg(v___f_3298_, v_msgData_3305_, v_macroStack_3282_);
                v___x_3307_ = lean_apply_2(v_toPure_3296_, lean_box(0), v___x_3306_);
                return v___x_3307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___redArg___lam__1___boxed(
    mut v___x_3311_: *mut LeanObject,
    mut v_toApplicative_3312_: *mut LeanObject,
    mut v_msgData_3313_: *mut LeanObject,
    mut v_macroStack_3314_: *mut LeanObject,
    mut v_____do__lift_3315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3316_: *mut LeanObject = core::ptr::null_mut();
    v_res_3316_ = l_Lean_Elab_addMacroStack___redArg___lam__1(
        v___x_3311_,
        v_toApplicative_3312_,
        v_msgData_3313_,
        v_macroStack_3314_,
        v_____do__lift_3315_,
    );
    lean_dec_ref(v_____do__lift_3315_);
    return v_res_3316_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___redArg(
    mut v_inst_3317_: *mut LeanObject,
    mut v_inst_3318_: *mut LeanObject,
    mut v_msgData_3319_: *mut LeanObject,
    mut v_macroStack_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    v___x_3321_ = l_Lean_KVMap_instValueBool;
    v_toApplicative_3322_ = lean_ctor_get(v_inst_3317_, 0);
    lean_inc_ref(v_toApplicative_3322_);
    v_toBind_3323_ = lean_ctor_get(v_inst_3317_, 1);
    lean_inc(v_toBind_3323_);
    lean_dec_ref(v_inst_3317_);
    v___f_3324_ = lean_alloc_closure(
        l_Lean_Elab_addMacroStack___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_3324_, 0, v___x_3321_);
    lean_closure_set(v___f_3324_, 1, v_toApplicative_3322_);
    lean_closure_set(v___f_3324_, 2, v_msgData_3319_);
    lean_closure_set(v___f_3324_, 3, v_macroStack_3320_);
    v___x_3325_ = lean_apply_4(
        v_toBind_3323_,
        lean_box(0),
        lean_box(0),
        v_inst_3318_,
        v___f_3324_,
    );
    return v___x_3325_;
}
pub unsafe fn l_Lean_Elab_addMacroStack(
    mut v_m_3326_: *mut LeanObject,
    mut v_inst_3327_: *mut LeanObject,
    mut v_inst_3328_: *mut LeanObject,
    mut v_msgData_3329_: *mut LeanObject,
    mut v_macroStack_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    v___x_3331_ = l_Lean_Elab_addMacroStack___redArg(
        v_inst_3327_,
        v_inst_3328_,
        v_msgData_3329_,
        v_macroStack_3330_,
    );
    return v___x_3331_;
}
pub unsafe fn _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    v___x_3333_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__0;
    v___x_3334_ = l_Lean_stringToMessageData(v___x_3333_);
    return v___x_3334_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0(
    mut v_inst_3335_: *mut LeanObject,
    mut v_inst_3336_: *mut LeanObject,
    mut v_____r_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    v___x_3338_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1_once),
        _init_l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0___closed__1,
    );
    v___x_3339_ = l_Lean_throwError___redArg(v_inst_3335_, v_inst_3336_, v___x_3338_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1(
    mut v_k_3340_: *mut LeanObject,
    mut v___f_3341_: *mut LeanObject,
    mut v_toApplicative_3342_: *mut LeanObject,
    mut v_____do__lift_3343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3344_: u8 = 0;
    lean_inc(v_k_3340_);
    v___x_3344_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_3343_, v_k_3340_);
    if v___x_3344_ == 0 {
        let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_3342_);
        lean_dec(v_k_3340_);
        v___x_3345_ = lean_box(0);
        v___x_3346_ = lean_apply_1(v___f_3341_, v___x_3345_);
        return v___x_3346_;
    } else {
        let mut v_toPure_3347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_3341_);
        v_toPure_3347_ = lean_ctor_get(v_toApplicative_3342_, 1);
        lean_inc(v_toPure_3347_);
        lean_dec_ref(v_toApplicative_3342_);
        v___x_3348_ = lean_apply_2(v_toPure_3347_, lean_box(0), v_k_3340_);
        return v___x_3348_;
    }
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(
    mut v_k_3349_: *mut LeanObject,
    mut v___f_3350_: *mut LeanObject,
    mut v_toApplicative_3351_: *mut LeanObject,
    mut v_toBind_3352_: *mut LeanObject,
    mut v_getEnv_3353_: *mut LeanObject,
    mut v_____do__lift_3354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    v_k_3355_ = l_Lean_mkPrivateName(v_____do__lift_3354_, v_k_3349_);
    v___f_3356_ = lean_alloc_closure(
        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3356_, 0, v_k_3355_);
    lean_closure_set(v___f_3356_, 1, v___f_3350_);
    lean_closure_set(v___f_3356_, 2, v_toApplicative_3351_);
    v___x_3357_ = lean_apply_4(
        v_toBind_3352_,
        lean_box(0),
        lean_box(0),
        v_getEnv_3353_,
        v___f_3356_,
    );
    return v___x_3357_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed(
    mut v_k_3358_: *mut LeanObject,
    mut v___f_3359_: *mut LeanObject,
    mut v_toApplicative_3360_: *mut LeanObject,
    mut v_toBind_3361_: *mut LeanObject,
    mut v_getEnv_3362_: *mut LeanObject,
    mut v_____do__lift_3363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3364_: *mut LeanObject = core::ptr::null_mut();
    v_res_3364_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2(
        v_k_3358_,
        v___f_3359_,
        v_toApplicative_3360_,
        v_toBind_3361_,
        v_getEnv_3362_,
        v_____do__lift_3363_,
    );
    lean_dec_ref(v_____do__lift_3363_);
    return v_res_3364_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(
    mut v___f_3365_: *mut LeanObject,
    mut v_k_3366_: *mut LeanObject,
    mut v_toBind_3367_: *mut LeanObject,
    mut v_getEnv_3368_: *mut LeanObject,
    mut v___f_3369_: *mut LeanObject,
    mut v___x_3370_: u8,
    mut v_____do__lift_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: u8 = 0;
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isExporting_3379_ = lean_ctor_get_uint8(
                    v_____do__lift_3371_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                if v_isExporting_3379_ == 0 {
                    state = 2;
                    continue;
                } else {
                    if v___x_3370_ == 0 {
                        lean_dec(v___f_3369_);
                        lean_dec(v_getEnv_3368_);
                        lean_dec(v_toBind_3367_);
                        state = 1;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3373_ = lean_box(0);
                v___x_3374_ = lean_apply_1(v___f_3365_, v___x_3373_);
                return v___x_3374_;
            }
            2 => {
                v___x_3376_ = l_Lean_isPrivateName(v_k_3366_);
                if v___x_3376_ == 0 {
                    lean_dec(v___f_3365_);
                    v___x_3377_ = lean_apply_4(
                        v_toBind_3367_,
                        lean_box(0),
                        lean_box(0),
                        v_getEnv_3368_,
                        v___f_3369_,
                    );
                    return v___x_3377_;
                } else {
                    if v___x_3370_ == 0 {
                        lean_dec(v___f_3369_);
                        lean_dec(v_getEnv_3368_);
                        lean_dec(v_toBind_3367_);
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___f_3365_);
                        v___x_3378_ = lean_apply_4(
                            v_toBind_3367_,
                            lean_box(0),
                            lean_box(0),
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
    mut v___f_3380_: *mut LeanObject,
    mut v_k_3381_: *mut LeanObject,
    mut v_toBind_3382_: *mut LeanObject,
    mut v_getEnv_3383_: *mut LeanObject,
    mut v___f_3384_: *mut LeanObject,
    mut v___x_3385_: *mut LeanObject,
    mut v_____do__lift_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_388__boxed_3387_: u8 = 0;
    let mut v_res_3388_: *mut LeanObject = core::ptr::null_mut();
    v___x_388__boxed_3387_ = (lean_unbox(v___x_3385_) as u8);
    v_res_3388_ = l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3(
        v___f_3380_,
        v_k_3381_,
        v_toBind_3382_,
        v_getEnv_3383_,
        v___f_3384_,
        v___x_388__boxed_3387_,
        v_____do__lift_3386_,
    );
    lean_dec_ref(v_____do__lift_3386_);
    lean_dec(v_k_3381_);
    return v_res_3388_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4(
    mut v_k_3389_: *mut LeanObject,
    mut v___f_3390_: *mut LeanObject,
    mut v_toBind_3391_: *mut LeanObject,
    mut v_getEnv_3392_: *mut LeanObject,
    mut v___f_3393_: *mut LeanObject,
    mut v_toApplicative_3394_: *mut LeanObject,
    mut v_____do__lift_3395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3396_: u8 = 0;
    lean_inc(v_k_3389_);
    v___x_3396_ = l_Lean_Parser_isValidSyntaxNodeKind(v_____do__lift_3395_, v_k_3389_);
    if v___x_3396_ == 0 {
        let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_3394_);
        v___x_3397_ = lean_box((v___x_3396_) as usize);
        lean_inc(v_getEnv_3392_);
        lean_inc(v_toBind_3391_);
        v___f_3398_ = lean_alloc_closure(
            l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__3___boxed as *mut core::ffi::c_void,
            7,
            6,
        );
        lean_closure_set(v___f_3398_, 0, v___f_3390_);
        lean_closure_set(v___f_3398_, 1, v_k_3389_);
        lean_closure_set(v___f_3398_, 2, v_toBind_3391_);
        lean_closure_set(v___f_3398_, 3, v_getEnv_3392_);
        lean_closure_set(v___f_3398_, 4, v___f_3393_);
        lean_closure_set(v___f_3398_, 5, v___x_3397_);
        v___x_3399_ = lean_apply_4(
            v_toBind_3391_,
            lean_box(0),
            lean_box(0),
            v_getEnv_3392_,
            v___f_3398_,
        );
        return v___x_3399_;
    } else {
        let mut v_toPure_3400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_3393_);
        lean_dec(v_getEnv_3392_);
        lean_dec(v_toBind_3391_);
        lean_dec(v___f_3390_);
        v_toPure_3400_ = lean_ctor_get(v_toApplicative_3394_, 1);
        lean_inc(v_toPure_3400_);
        lean_dec_ref(v_toApplicative_3394_);
        v___x_3401_ = lean_apply_2(v_toPure_3400_, lean_box(0), v_k_3389_);
        return v___x_3401_;
    }
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___redArg(
    mut v_inst_3402_: *mut LeanObject,
    mut v_inst_3403_: *mut LeanObject,
    mut v_inst_3404_: *mut LeanObject,
    mut v_k_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3406_ = lean_ctor_get(v_inst_3402_, 0);
    lean_inc_ref_n(v_toApplicative_3406_, 2);
    v_toBind_3407_ = lean_ctor_get(v_inst_3402_, 1);
    lean_inc_n(v_toBind_3407_, 3);
    v_getEnv_3408_ = lean_ctor_get(v_inst_3403_, 0);
    lean_inc_n(v_getEnv_3408_, 3);
    lean_dec_ref(v_inst_3403_);
    v___f_3409_ = lean_alloc_closure(
        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3409_, 0, v_inst_3402_);
    lean_closure_set(v___f_3409_, 1, v_inst_3404_);
    lean_inc_ref(v___f_3409_);
    lean_inc(v_k_3405_);
    v___f_3410_ = lean_alloc_closure(
        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_3410_, 0, v_k_3405_);
    lean_closure_set(v___f_3410_, 1, v___f_3409_);
    lean_closure_set(v___f_3410_, 2, v_toApplicative_3406_);
    lean_closure_set(v___f_3410_, 3, v_toBind_3407_);
    lean_closure_set(v___f_3410_, 4, v_getEnv_3408_);
    v___f_3411_ = lean_alloc_closure(
        l_Lean_Elab_checkSyntaxNodeKind___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_3411_, 0, v_k_3405_);
    lean_closure_set(v___f_3411_, 1, v___f_3409_);
    lean_closure_set(v___f_3411_, 2, v_toBind_3407_);
    lean_closure_set(v___f_3411_, 3, v_getEnv_3408_);
    lean_closure_set(v___f_3411_, 4, v___f_3410_);
    lean_closure_set(v___f_3411_, 5, v_toApplicative_3406_);
    v___x_3412_ = lean_apply_4(
        v_toBind_3407_,
        lean_box(0),
        lean_box(0),
        v_getEnv_3408_,
        v___f_3411_,
    );
    return v___x_3412_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind(
    mut v_m_3413_: *mut LeanObject,
    mut v_inst_3414_: *mut LeanObject,
    mut v_inst_3415_: *mut LeanObject,
    mut v_inst_3416_: *mut LeanObject,
    mut v_k_3417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    v___x_3418_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(
        v_inst_3414_,
        v_inst_3415_,
        v_inst_3416_,
        v_k_3417_,
    );
    return v___x_3418_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed(
    mut v_inst_3419_: *mut LeanObject,
    mut v_inst_3420_: *mut LeanObject,
    mut v_inst_3421_: *mut LeanObject,
    mut v_k_3422_: *mut LeanObject,
    mut v_pre_3423_: *mut LeanObject,
    mut v_x_3424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3425_: *mut LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0(
        v_inst_3419_,
        v_inst_3420_,
        v_inst_3421_,
        v_k_3422_,
        v_pre_3423_,
        v_x_3424_,
    );
    lean_dec_ref(v_x_3424_);
    return v_res_3425_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg(
    mut v_inst_3426_: *mut LeanObject,
    mut v_inst_3427_: *mut LeanObject,
    mut v_inst_3428_: *mut LeanObject,
    mut v_k_3429_: *mut LeanObject,
    mut v_x_3430_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3430_) {
        1 => {
            let mut v_toMonadExceptOf_3431_: *mut LeanObject = core::ptr::null_mut();
            let mut v_pre_3432_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tryCatch_3433_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3434_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
            v_toMonadExceptOf_3431_ = lean_ctor_get(v_inst_3428_, 0);
            v_pre_3432_ = lean_ctor_get(v_x_3430_, 0);
            v_tryCatch_3433_ = lean_ctor_get(v_toMonadExceptOf_3431_, 1);
            lean_inc(v_tryCatch_3433_);
            lean_inc(v_pre_3432_);
            lean_inc(v_k_3429_);
            lean_inc_ref(v_inst_3428_);
            lean_inc_ref(v_inst_3427_);
            lean_inc_ref(v_inst_3426_);
            v___f_3434_ = lean_alloc_closure(
                l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_3434_, 0, v_inst_3426_);
            lean_closure_set(v___f_3434_, 1, v_inst_3427_);
            lean_closure_set(v___f_3434_, 2, v_inst_3428_);
            lean_closure_set(v___f_3434_, 3, v_k_3429_);
            lean_closure_set(v___f_3434_, 4, v_pre_3432_);
            v___x_3435_ = l_Lean_Name_append(v_x_3430_, v_k_3429_);
            v___x_3436_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(
                v_inst_3426_,
                v_inst_3427_,
                v_inst_3428_,
                v___x_3435_,
            );
            v___x_3437_ = lean_apply_3(v_tryCatch_3433_, lean_box(0), v___x_3436_, v___f_3434_);
            return v___x_3437_;
        }
        0 => {
            let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
            v___x_3438_ = l_Lean_Elab_checkSyntaxNodeKind___redArg(
                v_inst_3426_,
                v_inst_3427_,
                v_inst_3428_,
                v_k_3429_,
            );
            return v___x_3438_;
        }
        _ => {
            let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_3430_);
            lean_dec(v_k_3429_);
            lean_dec_ref(v_inst_3427_);
            v___x_3439_ = lean_obj_once(
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
    mut v_inst_3441_: *mut LeanObject,
    mut v_inst_3442_: *mut LeanObject,
    mut v_inst_3443_: *mut LeanObject,
    mut v_k_3444_: *mut LeanObject,
    mut v_pre_3445_: *mut LeanObject,
    mut v_x_3446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_3448_: *mut LeanObject,
    mut v_inst_3449_: *mut LeanObject,
    mut v_inst_3450_: *mut LeanObject,
    mut v_inst_3451_: *mut LeanObject,
    mut v_k_3452_: *mut LeanObject,
    mut v_x_3453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    v___x_3455_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3455_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    v___x_3456_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__0);
    v___x_3457_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3457_, 0, v___x_3456_);
    return v___x_3457_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    v___x_3458_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
    v___x_3459_ = lean_unsigned_to_nat(0);
    v___x_3460_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3460_, 0, v___x_3459_);
    lean_ctor_set(v___x_3460_, 1, v___x_3459_);
    lean_ctor_set(v___x_3460_, 2, v___x_3459_);
    lean_ctor_set(v___x_3460_, 3, v___x_3459_);
    lean_ctor_set(v___x_3460_, 4, v___x_3458_);
    lean_ctor_set(v___x_3460_, 5, v___x_3458_);
    lean_ctor_set(v___x_3460_, 6, v___x_3458_);
    lean_ctor_set(v___x_3460_, 7, v___x_3458_);
    lean_ctor_set(v___x_3460_, 8, v___x_3458_);
    lean_ctor_set(v___x_3460_, 9, v___x_3458_);
    return v___x_3460_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    v___x_3461_ = lean_unsigned_to_nat(32);
    v___x_3462_ = lean_mk_empty_array_with_capacity(v___x_3461_);
    v___x_3463_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3463_, 0, v___x_3462_);
    return v___x_3463_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_3464_: usize = 0;
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    v___x_3464_ = 5usize;
    v___x_3465_ = lean_unsigned_to_nat(0);
    v___x_3466_ = lean_unsigned_to_nat(32);
    v___x_3467_ = lean_mk_empty_array_with_capacity(v___x_3466_);
    v___x_3468_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__3);
    v___x_3469_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3469_, 0, v___x_3468_);
    lean_ctor_set(v___x_3469_, 1, v___x_3467_);
    lean_ctor_set(v___x_3469_, 2, v___x_3465_);
    lean_ctor_set(v___x_3469_, 3, v___x_3465_);
    lean_ctor_set_usize(v___x_3469_, 4, v___x_3464_);
    return v___x_3469_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5()
-> *mut LeanObject {
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    v___x_3470_ = lean_box(1);
    v___x_3471_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__4);
    v___x_3472_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__1);
    v___x_3473_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3473_, 0, v___x_3472_);
    lean_ctor_set(v___x_3473_, 1, v___x_3471_);
    lean_ctor_set(v___x_3473_, 2, v___x_3470_);
    return v___x_3473_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(
    mut v_msgData_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    v___x_3478_ = lean_st_ref_get(v___y_3476_);
    v_env_3479_ = lean_ctor_get(v___x_3478_, 0);
    lean_inc_ref(v_env_3479_);
    lean_dec(v___x_3478_);
    v_options_3480_ = lean_ctor_get(v___y_3475_, 2);
    v___x_3481_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
    v___x_3482_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
    lean_inc_ref(v_options_3480_);
    v___x_3483_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3483_, 0, v_env_3479_);
    lean_ctor_set(v___x_3483_, 1, v___x_3481_);
    lean_ctor_set(v___x_3483_, 2, v___x_3482_);
    lean_ctor_set(v___x_3483_, 3, v_options_3480_);
    v___x_3484_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3484_, 0, v___x_3483_);
    lean_ctor_set(v___x_3484_, 1, v_msgData_3474_);
    v___x_3485_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3485_, 0, v___x_3484_);
    return v___x_3485_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___boxed(
    mut v_msgData_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
    mut v___y_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3490_: *mut LeanObject = core::ptr::null_mut();
    v_res_3490_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msgData_3486_, v___y_3487_, v___y_3488_);
    lean_dec(v___y_3488_);
    lean_dec_ref(v___y_3487_);
    return v_res_3490_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(
    mut v_msg_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3500_: u8 = 0;
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3495_ = lean_ctor_get(v___y_3492_, 5);
                v___x_3496_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_3491_, v___y_3492_, v___y_3493_);
                v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
                v_isSharedCheck_3505_ = (!lean_is_exclusive(v___x_3496_)) as u8;
                if v_isSharedCheck_3505_ == 0 {
                    v___x_3499_ = v___x_3496_;
                    v_isShared_3500_ = v_isSharedCheck_3505_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3497_);
                    lean_dec(v___x_3496_);
                    v___x_3499_ = lean_box(0);
                    v_isShared_3500_ = v_isSharedCheck_3505_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3495_);
                v___x_3501_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3501_, 0, v_ref_3495_);
                lean_ctor_set(v___x_3501_, 1, v_a_3497_);
                if v_isShared_3500_ == 0 {
                    lean_ctor_set_tag(v___x_3499_, 1);
                    lean_ctor_set(v___x_3499_, 0, v___x_3501_);
                    v___x_3503_ = v___x_3499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
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
    mut v_msg_3506_: *mut LeanObject,
    mut v___y_3507_: *mut LeanObject,
    mut v___y_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3510_: *mut LeanObject = core::ptr::null_mut();
    v_res_3510_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_3506_, v___y_3507_, v___y_3508_);
    lean_dec(v___y_3508_);
    lean_dec_ref(v___y_3507_);
    return v_res_3510_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(
    mut v_k_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3520_ = lean_st_ref_get(v___y_3513_);
                v_env_3521_ = lean_ctor_get(v___x_3520_, 0);
                lean_inc_ref(v_env_3521_);
                lean_dec(v___x_3520_);
                lean_inc(v_k_3511_);
                v___x_3522_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3521_, v_k_3511_);
                if v___x_3522_ == 0 {
                    v___x_3523_ = lean_st_ref_get(v___y_3513_);
                    v_env_3540_ = lean_ctor_get(v___x_3523_, 0);
                    lean_inc_ref(v_env_3540_);
                    lean_dec(v___x_3523_);
                    v_isExporting_3541_ = lean_ctor_get_uint8(
                        v_env_3540_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    lean_dec_ref(v_env_3540_);
                    if v_isExporting_3541_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        if v___x_3522_ == 0 {
                            lean_dec(v_k_3511_);
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
                    v___x_3542_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3542_, 0, v_k_3511_);
                    return v___x_3542_;
                }
            }
            1 => {
                v___x_3518_ = lean_obj_once(
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
                    v_env_3527_ = lean_ctor_get(v___x_3526_, 0);
                    lean_inc_ref(v_env_3527_);
                    lean_dec(v___x_3526_);
                    v___x_3528_ = lean_st_ref_get(v___y_3513_);
                    v_env_3529_ = lean_ctor_get(v___x_3528_, 0);
                    lean_inc_ref(v_env_3529_);
                    lean_dec(v___x_3528_);
                    v_k_3530_ = l_Lean_mkPrivateName(v_env_3527_, v_k_3511_);
                    lean_dec_ref(v_env_3527_);
                    lean_inc(v_k_3530_);
                    v___x_3531_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3529_, v_k_3530_);
                    if v___x_3531_ == 0 {
                        lean_dec(v_k_3530_);
                        v___y_3516_ = v___y_3512_;
                        v___y_3517_ = v___y_3513_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3532_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3532_, 0, v_k_3530_);
                        return v___x_3532_;
                    }
                } else {
                    if v___x_3522_ == 0 {
                        lean_dec(v_k_3511_);
                        v___y_3516_ = v___y_3512_;
                        v___y_3517_ = v___y_3513_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3533_ = lean_st_ref_get(v___y_3513_);
                        v_env_3534_ = lean_ctor_get(v___x_3533_, 0);
                        lean_inc_ref(v_env_3534_);
                        lean_dec(v___x_3533_);
                        v___x_3535_ = lean_st_ref_get(v___y_3513_);
                        v_env_3536_ = lean_ctor_get(v___x_3535_, 0);
                        lean_inc_ref(v_env_3536_);
                        lean_dec(v___x_3535_);
                        v_k_3537_ = l_Lean_mkPrivateName(v_env_3534_, v_k_3511_);
                        lean_dec_ref(v_env_3534_);
                        lean_inc(v_k_3537_);
                        v___x_3538_ = l_Lean_Parser_isValidSyntaxNodeKind(v_env_3536_, v_k_3537_);
                        if v___x_3538_ == 0 {
                            lean_dec(v_k_3537_);
                            v___y_3516_ = v___y_3512_;
                            v___y_3517_ = v___y_3513_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3539_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3539_, 0, v_k_3537_);
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
    mut v_k_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3547_: *mut LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v_k_3543_, v___y_3544_, v___y_3545_);
    lean_dec(v___y_3545_);
    lean_dec_ref(v___y_3544_);
    return v_res_3547_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(
    mut v_k_3548_: *mut LeanObject,
    mut v_x_3549_: *mut LeanObject,
    mut v___y_3550_: *mut LeanObject,
    mut v___y_3551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pre_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3558_: u8 = 0;
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: u8 = 0;
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3549_) {
                1 => {
                    v_pre_3553_ = lean_ctor_get(v_x_3549_, 0);
                    lean_inc(v_pre_3553_);
                    lean_inc(v_k_3548_);
                    v___x_3554_ = l_Lean_Name_append(v_x_3549_, v_k_3548_);
                    v___x_3555_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_3554_, v___y_3550_, v___y_3551_);
                    if lean_obj_tag(v___x_3555_) == 0 {
                        lean_dec(v_pre_3553_);
                        lean_dec(v_k_3548_);
                        return v___x_3555_;
                    } else {
                        v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
                        lean_inc(v_a_3556_);
                        v___x_3560_ = l_Lean_Exception_isInterrupt(v_a_3556_);
                        if v___x_3560_ == 0 {
                            v___x_3561_ = l_Lean_Exception_isRuntime(v_a_3556_);
                            v___y_3558_ = v___x_3561_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_3556_);
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
                    lean_dec(v_x_3549_);
                    lean_dec(v_k_3548_);
                    v___x_3563_ = lean_obj_once(
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
                    lean_dec_ref_known(v___x_3555_, 1);
                    v_x_3549_ = v_pre_3553_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_pre_3553_);
                    lean_dec(v_k_3548_);
                    return v___x_3555_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0___boxed(
    mut v_k_3565_: *mut LeanObject,
    mut v_x_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3570_: *mut LeanObject = core::ptr::null_mut();
    v_res_3570_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_3565_, v_x_3566_, v___y_3567_, v___y_3568_);
    lean_dec(v___y_3568_);
    lean_dec_ref(v___y_3567_);
    return v_res_3570_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(
    mut v_k_3571_: *mut LeanObject,
    mut v_a_3572_: *mut LeanObject,
    mut v_a_3573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    v_currNamespace_3575_ = lean_ctor_get(v_a_3572_, 6);
    lean_inc(v_currNamespace_3575_);
    v___x_3576_ = l_Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0(v_k_3571_, v_currNamespace_3575_, v_a_3572_, v_a_3573_);
    return v___x_3576_;
}
pub unsafe fn l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces___boxed(
    mut v_k_3577_: *mut LeanObject,
    mut v_a_3578_: *mut LeanObject,
    mut v_a_3579_: *mut LeanObject,
    mut v_a_3580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3581_: *mut LeanObject = core::ptr::null_mut();
    v_res_3581_ =
        l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(v_k_3577_, v_a_3578_, v_a_3579_);
    lean_dec(v_a_3579_);
    lean_dec_ref(v_a_3578_);
    return v_res_3581_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(
    mut v_00_u03b1_3582_: *mut LeanObject,
    mut v_msg_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    v___x_3587_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_3583_, v___y_3584_, v___y_3585_);
    return v___x_3587_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___boxed(
    mut v_00_u03b1_3588_: *mut LeanObject,
    mut v_msg_3589_: *mut LeanObject,
    mut v___y_3590_: *mut LeanObject,
    mut v___y_3591_: *mut LeanObject,
    mut v___y_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3593_: *mut LeanObject = core::ptr::null_mut();
    v_res_3593_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1(v_00_u03b1_3588_, v_msg_3589_, v___y_3590_, v___y_3591_);
    lean_dec(v___y_3591_);
    lean_dec_ref(v___y_3590_);
    return v_res_3593_;
}
pub unsafe fn _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1() -> *mut LeanObject {
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    v___x_3595_ = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__0;
    v___x_3596_ = l_Lean_stringToMessageData(v___x_3595_);
    return v___x_3596_;
}
pub unsafe fn _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3() -> *mut LeanObject {
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__2;
    v___x_3599_ = l_Lean_stringToMessageData(v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Lean_Elab_syntaxNodeKindOfAttrParam(
    mut v_defaultParserNamespace_3600_: *mut LeanObject,
    mut v_stx_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3609_: u8 = 0;
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3619_: u8 = 0;
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___x_3624_: u8 = 0;
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3605_ = l_Lean_Attribute_Builtin_getId(v_stx_3601_, v_a_3602_, v_a_3603_);
                if lean_obj_tag(v___x_3605_) == 0 {
                    v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
                    lean_inc_n(v_a_3606_, 2);
                    lean_dec_ref_known(v___x_3605_, 1);
                    v___x_3616_ = l_Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces(
                        v_a_3606_, v_a_3602_, v_a_3603_,
                    );
                    if lean_obj_tag(v___x_3616_) == 0 {
                        lean_dec(v_a_3606_);
                        lean_dec(v_defaultParserNamespace_3600_);
                        return v___x_3616_;
                    } else {
                        v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
                        lean_inc(v_a_3617_);
                        v___x_3625_ = l_Lean_Exception_isInterrupt(v_a_3617_);
                        if v___x_3625_ == 0 {
                            v___x_3626_ = l_Lean_Exception_isRuntime(v_a_3617_);
                            v___y_3619_ = v___x_3626_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_a_3617_);
                            v___y_3619_ = v___x_3625_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_defaultParserNamespace_3600_);
                    return v___x_3605_;
                }
            }
            1 => {
                if v___y_3609_ == 0 {
                    lean_dec_ref(v___y_3608_);
                    v___x_3610_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1_once
                        ),
                        _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__1,
                    );
                    v___x_3611_ = l_Lean_MessageData_ofName(v_a_3606_);
                    v___x_3612_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3612_, 0, v___x_3610_);
                    lean_ctor_set(v___x_3612_, 1, v___x_3611_);
                    v___x_3613_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once
                        ),
                        _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3,
                    );
                    v___x_3614_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3614_, 0, v___x_3612_);
                    lean_ctor_set(v___x_3614_, 1, v___x_3613_);
                    v___x_3615_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v___x_3614_, v_a_3602_, v_a_3603_);
                    return v___x_3615_;
                } else {
                    lean_dec(v_a_3606_);
                    return v___y_3608_;
                }
            }
            2 => {
                if v___y_3619_ == 0 {
                    lean_dec_ref_known(v___x_3616_, 1);
                    lean_inc(v_a_3606_);
                    v___x_3620_ = l_Lean_Name_append(v_defaultParserNamespace_3600_, v_a_3606_);
                    v___x_3621_ = l_Lean_Elab_checkSyntaxNodeKind___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__0(v___x_3620_, v_a_3602_, v_a_3603_);
                    if lean_obj_tag(v___x_3621_) == 0 {
                        lean_dec(v_a_3606_);
                        return v___x_3621_;
                    } else {
                        v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
                        lean_inc(v_a_3622_);
                        v___x_3623_ = l_Lean_Exception_isInterrupt(v_a_3622_);
                        if v___x_3623_ == 0 {
                            v___x_3624_ = l_Lean_Exception_isRuntime(v_a_3622_);
                            v___y_3608_ = v___x_3621_;
                            v___y_3609_ = v___x_3624_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_3622_);
                            v___y_3608_ = v___x_3621_;
                            v___y_3609_ = v___x_3623_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3606_);
                    lean_dec(v_defaultParserNamespace_3600_);
                    return v___x_3616_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_syntaxNodeKindOfAttrParam___boxed(
    mut v_defaultParserNamespace_3627_: *mut LeanObject,
    mut v_stx_3628_: *mut LeanObject,
    mut v_a_3629_: *mut LeanObject,
    mut v_a_3630_: *mut LeanObject,
    mut v_a_3631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3632_: *mut LeanObject = core::ptr::null_mut();
    v_res_3632_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(
        v_defaultParserNamespace_3627_,
        v_stx_3628_,
        v_a_3629_,
        v_a_3630_,
    );
    lean_dec(v_a_3630_);
    lean_dec_ref(v_a_3629_);
    return v_res_3632_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(
    mut v_env_3637_: *mut LeanObject,
    mut v_opts_3638_: *mut LeanObject,
    mut v_constName_3639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_env_3642_: *mut LeanObject,
    mut v_opts_3643_: *mut LeanObject,
    mut v_constName_3644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3645_: *mut LeanObject = core::ptr::null_mut();
    v_res_3645_ = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(
        v_env_3642_,
        v_opts_3643_,
        v_constName_3644_,
    );
    lean_dec_ref(v_opts_3643_);
    return v_res_3645_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10() -> *mut LeanObject {
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    v___x_3670_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__8;
    v___x_3671_ = l_Lean_mkAtom(v___x_3670_);
    return v___x_3671_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11() -> *mut LeanObject {
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    v___x_3672_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__10_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__10,
    );
    v___x_3673_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3674_ = lean_array_push(v___x_3673_, v___x_3672_);
    return v___x_3674_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    v___x_3683_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__15;
    v___x_3684_ = l_Lean_mkAtom(v___x_3683_);
    return v___x_3684_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    v___x_3685_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__16_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__16,
    );
    v___x_3686_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3687_ = lean_array_push(v___x_3686_, v___x_3685_);
    return v___x_3687_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    v___x_3688_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__17_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__17,
    );
    v___x_3689_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__14;
    v___x_3690_ = lean_box(2);
    v___x_3691_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3691_, 0, v___x_3690_);
    lean_ctor_set(v___x_3691_, 1, v___x_3689_);
    lean_ctor_set(v___x_3691_, 2, v___x_3688_);
    return v___x_3691_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    v___x_3692_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__18_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__18,
    );
    v___x_3693_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__11_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__11,
    );
    v___x_3694_ = lean_array_push(v___x_3693_, v___x_3692_);
    return v___x_3694_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    v___x_3695_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__19_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__19,
    );
    v___x_3696_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__9;
    v___x_3697_ = lean_box(2);
    v___x_3698_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3698_, 0, v___x_3697_);
    lean_ctor_set(v___x_3698_, 1, v___x_3696_);
    lean_ctor_set(v___x_3698_, 2, v___x_3695_);
    return v___x_3698_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3699_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__20_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__20,
    );
    v___x_3700_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3701_ = lean_array_push(v___x_3700_, v___x_3699_);
    return v___x_3701_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    v___x_3702_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__21_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__21,
    );
    v___x_3703_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__7;
    v___x_3704_ = lean_box(2);
    v___x_3705_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3705_, 0, v___x_3704_);
    lean_ctor_set(v___x_3705_, 1, v___x_3703_);
    lean_ctor_set(v___x_3705_, 2, v___x_3702_);
    return v___x_3705_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    v___x_3706_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__22_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__22,
    );
    v___x_3707_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3708_ = lean_array_push(v___x_3707_, v___x_3706_);
    return v___x_3708_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    v___x_3709_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__23_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__23,
    );
    v___x_3710_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__5;
    v___x_3711_ = lean_box(2);
    v___x_3712_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3712_, 0, v___x_3711_);
    lean_ctor_set(v___x_3712_, 1, v___x_3710_);
    lean_ctor_set(v___x_3712_, 2, v___x_3709_);
    return v___x_3712_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    v___x_3713_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__24_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__24,
    );
    v___x_3714_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__3;
    v___x_3715_ = lean_array_push(v___x_3714_, v___x_3713_);
    return v___x_3715_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    v___x_3716_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__25_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__25,
    );
    v___x_3717_ = l_Lean_Elab_mkElabAttribute___auto__1___closed__2;
    v___x_3718_ = lean_box(2);
    v___x_3719_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_3719_, 0, v___x_3718_);
    lean_ctor_set(v___x_3719_, 1, v___x_3717_);
    lean_ctor_set(v___x_3719_, 2, v___x_3716_);
    return v___x_3719_;
}
pub unsafe fn _init_l_Lean_Elab_mkElabAttribute___auto__1() -> *mut LeanObject {
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    v___x_3720_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Elab_mkElabAttribute___auto__1___closed__26_once),
        _init_l_Lean_Elab_mkElabAttribute___auto__1___closed__26,
    );
    return v___x_3720_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg___lam__0(
    mut v_builtin_3721_: u8,
    mut v_declName_3722_: *mut LeanObject,
    mut v_kind_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
) -> *mut LeanObject {
    if v_builtin_3721_ == 0 {
        let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_declName_3722_);
        v___x_3727_ = lean_box(0);
        v___x_3728_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3728_, 0, v___x_3727_);
        return v___x_3728_;
    } else {
        let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
        v___x_3729_ =
            l_Lean_declareBuiltinDocStringAndRanges(v_declName_3722_, v___y_3724_, v___y_3725_);
        return v___x_3729_;
    }
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg___lam__0___boxed(
    mut v_builtin_3730_: *mut LeanObject,
    mut v_declName_3731_: *mut LeanObject,
    mut v_kind_3732_: *mut LeanObject,
    mut v___y_3733_: *mut LeanObject,
    mut v___y_3734_: *mut LeanObject,
    mut v___y_3735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_builtin_boxed_3736_: u8 = 0;
    let mut v_res_3737_: *mut LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3736_ = (lean_unbox(v_builtin_3730_) as u8);
    v_res_3737_ = l_Lean_Elab_mkElabAttribute___redArg___lam__0(
        v_builtin_boxed_3736_,
        v_declName_3731_,
        v_kind_3732_,
        v___y_3733_,
        v___y_3734_,
    );
    lean_dec(v___y_3734_);
    lean_dec_ref(v___y_3733_);
    lean_dec(v_kind_3732_);
    return v_res_3737_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(
    mut v_t_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_3743_: u8 = 0;
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3758_: u8 = 0;
    let mut v_enabled_3759_: u8 = 0;
    let mut v_assignment_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_isSharedCheck_3777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3741_ = lean_st_ref_get(v___y_3739_);
                v_infoState_3742_ = lean_ctor_get(v___x_3741_, 7);
                lean_inc_ref(v_infoState_3742_);
                lean_dec(v___x_3741_);
                v_enabled_3743_ = lean_ctor_get_uint8(
                    v_infoState_3742_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_3742_);
                if v_enabled_3743_ == 0 {
                    lean_dec_ref(v_t_3738_);
                    v___x_3744_ = lean_box(0);
                    v___x_3745_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3745_, 0, v___x_3744_);
                    return v___x_3745_;
                } else {
                    v___x_3746_ = lean_st_ref_take(v___y_3739_);
                    v_infoState_3747_ = lean_ctor_get(v___x_3746_, 7);
                    v_env_3748_ = lean_ctor_get(v___x_3746_, 0);
                    v_nextMacroScope_3749_ = lean_ctor_get(v___x_3746_, 1);
                    v_ngen_3750_ = lean_ctor_get(v___x_3746_, 2);
                    v_auxDeclNGen_3751_ = lean_ctor_get(v___x_3746_, 3);
                    v_traceState_3752_ = lean_ctor_get(v___x_3746_, 4);
                    v_cache_3753_ = lean_ctor_get(v___x_3746_, 5);
                    v_messages_3754_ = lean_ctor_get(v___x_3746_, 6);
                    v_snapshotTasks_3755_ = lean_ctor_get(v___x_3746_, 8);
                    v_isSharedCheck_3777_ = (!lean_is_exclusive(v___x_3746_)) as u8;
                    if v_isSharedCheck_3777_ == 0 {
                        v___x_3757_ = v___x_3746_;
                        v_isShared_3758_ = v_isSharedCheck_3777_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_3755_);
                        lean_inc(v_infoState_3747_);
                        lean_inc(v_messages_3754_);
                        lean_inc(v_cache_3753_);
                        lean_inc(v_traceState_3752_);
                        lean_inc(v_auxDeclNGen_3751_);
                        lean_inc(v_ngen_3750_);
                        lean_inc(v_nextMacroScope_3749_);
                        lean_inc(v_env_3748_);
                        lean_dec(v___x_3746_);
                        v___x_3757_ = lean_box(0);
                        v_isShared_3758_ = v_isSharedCheck_3777_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_3759_ = lean_ctor_get_uint8(
                    v_infoState_3747_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_3760_ = lean_ctor_get(v_infoState_3747_, 0);
                v_lazyAssignment_3761_ = lean_ctor_get(v_infoState_3747_, 1);
                v_trees_3762_ = lean_ctor_get(v_infoState_3747_, 2);
                v_isSharedCheck_3776_ = (!lean_is_exclusive(v_infoState_3747_)) as u8;
                if v_isSharedCheck_3776_ == 0 {
                    v___x_3764_ = v_infoState_3747_;
                    v_isShared_3765_ = v_isSharedCheck_3776_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_trees_3762_);
                    lean_inc(v_lazyAssignment_3761_);
                    lean_inc(v_assignment_3760_);
                    lean_dec(v_infoState_3747_);
                    v___x_3764_ = lean_box(0);
                    v_isShared_3765_ = v_isSharedCheck_3776_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3766_ = l_Lean_PersistentArray_push___redArg(v_trees_3762_, v_t_3738_);
                if v_isShared_3765_ == 0 {
                    lean_ctor_set(v___x_3764_, 2, v___x_3766_);
                    v___x_3768_ = v___x_3764_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_assignment_3760_);
                    lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_lazyAssignment_3761_);
                    lean_ctor_set(v_reuseFailAlloc_3775_, 2, v___x_3766_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3775_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_3759_,
                    );
                    v___x_3768_ = v_reuseFailAlloc_3775_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3758_ == 0 {
                    lean_ctor_set(v___x_3757_, 7, v___x_3768_);
                    v___x_3770_ = v___x_3757_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_env_3748_);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_nextMacroScope_3749_);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_ngen_3750_);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 3, v_auxDeclNGen_3751_);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 4, v_traceState_3752_);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 5, v_cache_3753_);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 6, v_messages_3754_);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 7, v___x_3768_);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 8, v_snapshotTasks_3755_);
                    v___x_3770_ = v_reuseFailAlloc_3774_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3771_ = lean_st_ref_set(v___y_3739_, v___x_3770_);
                v___x_3772_ = lean_box(0);
                v___x_3773_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3773_, 0, v___x_3772_);
                return v___x_3773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg___boxed(
    mut v_t_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
    mut v___y_3780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3781_: *mut LeanObject = core::ptr::null_mut();
    v_res_3781_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_3778_, v___y_3779_);
    lean_dec(v___y_3779_);
    return v_res_3781_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    v___x_3782_ = lean_unsigned_to_nat(32);
    v___x_3783_ = lean_mk_empty_array_with_capacity(v___x_3782_);
    v___x_3784_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3784_, 0, v___x_3783_);
    return v___x_3784_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1()
-> *mut LeanObject {
    let mut v___x_3785_: usize = 0;
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    v___x_3785_ = 5usize;
    v___x_3786_ = lean_unsigned_to_nat(0);
    v___x_3787_ = lean_unsigned_to_nat(32);
    v___x_3788_ = lean_mk_empty_array_with_capacity(v___x_3787_);
    v___x_3789_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__0);
    v___x_3790_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3790_, 0, v___x_3789_);
    lean_ctor_set(v___x_3790_, 1, v___x_3788_);
    lean_ctor_set(v___x_3790_, 2, v___x_3786_);
    lean_ctor_set(v___x_3790_, 3, v___x_3786_);
    lean_ctor_set_usize(v___x_3790_, 4, v___x_3785_);
    return v___x_3790_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(
    mut v_t_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
    mut v___y_3793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_3797_: u8 = 0;
    v___x_3795_ = lean_st_ref_get(v___y_3793_);
    v_infoState_3796_ = lean_ctor_get(v___x_3795_, 7);
    lean_inc_ref(v_infoState_3796_);
    lean_dec(v___x_3795_);
    v_enabled_3797_ = lean_ctor_get_uint8(
        v_infoState_3796_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_infoState_3796_);
    if v_enabled_3797_ == 0 {
        let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_t_3791_);
        v___x_3798_ = lean_box(0);
        v___x_3799_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3799_, 0, v___x_3798_);
        return v___x_3799_;
    } else {
        let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
        v___x_3800_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___closed__1);
        v___x_3801_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3801_, 0, v_t_3791_);
        lean_ctor_set(v___x_3801_, 1, v___x_3800_);
        v___x_3802_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v___x_3801_, v___y_3793_);
        return v___x_3802_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5___boxed(
    mut v_t_3803_: *mut LeanObject,
    mut v___y_3804_: *mut LeanObject,
    mut v___y_3805_: *mut LeanObject,
    mut v___y_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3807_: *mut LeanObject = core::ptr::null_mut();
    v_res_3807_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v_t_3803_, v___y_3804_, v___y_3805_);
    lean_dec(v___y_3805_);
    lean_dec_ref(v___y_3804_);
    return v_res_3807_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    v___x_3809_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__0;
    v___x_3810_ = l_Lean_stringToMessageData(v___x_3809_);
    return v___x_3810_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__2;
    v___x_3813_ = l_Lean_stringToMessageData(v___x_3812_);
    return v___x_3813_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    v___x_3815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__4;
    v___x_3816_ = l_Lean_stringToMessageData(v___x_3815_);
    return v___x_3816_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    v___x_3818_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__6;
    v___x_3819_ = l_Lean_stringToMessageData(v___x_3818_);
    return v___x_3819_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__8;
    v___x_3822_ = l_Lean_stringToMessageData(v___x_3821_);
    return v___x_3822_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    v___x_3824_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__10;
    v___x_3825_ = l_Lean_stringToMessageData(v___x_3824_);
    return v___x_3825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__12;
    v___x_3828_ = l_Lean_stringToMessageData(v___x_3827_);
    return v___x_3828_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(
    mut v_msg_3829_: *mut LeanObject,
    mut v_declHint_3830_: *mut LeanObject,
    mut v___y_3831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: u8 = 0;
    let mut v_isExporting_3836_: u8 = 0;
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3858_: u8 = 0;
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3833_ = lean_st_ref_get(v___y_3831_);
                v_env_3834_ = lean_ctor_get(v___x_3833_, 0);
                lean_inc_ref(v_env_3834_);
                lean_dec(v___x_3833_);
                v___x_3835_ = l_Lean_Name_isAnonymous(v_declHint_3830_);
                if v___x_3835_ == 0 {
                    v_isExporting_3836_ = lean_ctor_get_uint8(
                        v_env_3834_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3836_ == 0 {
                        lean_dec_ref(v_env_3834_);
                        lean_dec(v_declHint_3830_);
                        v___x_3837_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3837_, 0, v_msg_3829_);
                        return v___x_3837_;
                    } else {
                        lean_inc_ref(v_env_3834_);
                        v___x_3838_ = l_Lean_Environment_setExporting(v_env_3834_, v___x_3835_);
                        lean_inc(v_declHint_3830_);
                        lean_inc_ref(v___x_3838_);
                        v___x_3839_ = l_Lean_Environment_contains(
                            v___x_3838_,
                            v_declHint_3830_,
                            v_isExporting_3836_,
                        );
                        if v___x_3839_ == 0 {
                            lean_dec_ref(v___x_3838_);
                            lean_dec_ref(v_env_3834_);
                            lean_dec(v_declHint_3830_);
                            v___x_3840_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3840_, 0, v_msg_3829_);
                            return v___x_3840_;
                        } else {
                            v___x_3841_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__2);
                            v___x_3842_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2___closed__5);
                            v___x_3843_ = l_Lean_Options_empty;
                            v___x_3844_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3844_, 0, v___x_3838_);
                            lean_ctor_set(v___x_3844_, 1, v___x_3841_);
                            lean_ctor_set(v___x_3844_, 2, v___x_3842_);
                            lean_ctor_set(v___x_3844_, 3, v___x_3843_);
                            lean_inc(v_declHint_3830_);
                            v___x_3845_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3830_, v___x_3835_);
                            v_c_3846_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3846_, 0, v___x_3844_);
                            lean_ctor_set(v_c_3846_, 1, v___x_3845_);
                            v___x_3847_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3834_,
                                v_declHint_3830_,
                            );
                            if lean_obj_tag(v___x_3847_) == 0 {
                                lean_dec_ref(v_env_3834_);
                                lean_dec(v_declHint_3830_);
                                v___x_3848_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
                                v___x_3849_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3849_, 0, v___x_3848_);
                                lean_ctor_set(v___x_3849_, 1, v_c_3846_);
                                v___x_3850_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
                                v___x_3851_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3851_, 0, v___x_3849_);
                                lean_ctor_set(v___x_3851_, 1, v___x_3850_);
                                v___x_3852_ = l_Lean_MessageData_note(v___x_3851_);
                                v___x_3853_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3853_, 0, v_msg_3829_);
                                lean_ctor_set(v___x_3853_, 1, v___x_3852_);
                                v___x_3854_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3854_, 0, v___x_3853_);
                                return v___x_3854_;
                            } else {
                                v_val_3855_ = lean_ctor_get(v___x_3847_, 0);
                                v_isSharedCheck_3890_ = (!lean_is_exclusive(v___x_3847_)) as u8;
                                if v_isSharedCheck_3890_ == 0 {
                                    v___x_3857_ = v___x_3847_;
                                    v_isShared_3858_ = v_isSharedCheck_3890_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3855_);
                                    lean_dec(v___x_3847_);
                                    v___x_3857_ = lean_box(0);
                                    v_isShared_3858_ = v_isSharedCheck_3890_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3834_);
                    lean_dec(v_declHint_3830_);
                    v___x_3891_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3891_, 0, v_msg_3829_);
                    return v___x_3891_;
                }
            }
            1 => {
                v___x_3859_ = lean_box(0);
                v___x_3860_ = l_Lean_Environment_header(v_env_3834_);
                lean_dec_ref(v_env_3834_);
                v___x_3861_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3860_);
                v_mod_3862_ = lean_array_get(v___x_3859_, v___x_3861_, v_val_3855_);
                lean_dec(v_val_3855_);
                lean_dec_ref(v___x_3861_);
                v___x_3863_ = l_Lean_isPrivateName(v_declHint_3830_);
                lean_dec(v_declHint_3830_);
                if v___x_3863_ == 0 {
                    v___x_3864_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
                    v___x_3865_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3865_, 0, v___x_3864_);
                    lean_ctor_set(v___x_3865_, 1, v_c_3846_);
                    v___x_3866_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
                    v___x_3867_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3867_, 0, v___x_3865_);
                    lean_ctor_set(v___x_3867_, 1, v___x_3866_);
                    v___x_3868_ = l_Lean_MessageData_ofName(v_mod_3862_);
                    v___x_3869_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3869_, 0, v___x_3867_);
                    lean_ctor_set(v___x_3869_, 1, v___x_3868_);
                    v___x_3870_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
                    v___x_3871_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3871_, 0, v___x_3869_);
                    lean_ctor_set(v___x_3871_, 1, v___x_3870_);
                    v___x_3872_ = l_Lean_MessageData_note(v___x_3871_);
                    v___x_3873_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3873_, 0, v_msg_3829_);
                    lean_ctor_set(v___x_3873_, 1, v___x_3872_);
                    if v_isShared_3858_ == 0 {
                        lean_ctor_set_tag(v___x_3857_, 0);
                        lean_ctor_set(v___x_3857_, 0, v___x_3873_);
                        v___x_3875_ = v___x_3857_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
                        v___x_3875_ = v_reuseFailAlloc_3876_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3877_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
                    v___x_3878_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3878_, 0, v___x_3877_);
                    lean_ctor_set(v___x_3878_, 1, v_c_3846_);
                    v___x_3879_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
                    v___x_3880_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3880_, 0, v___x_3878_);
                    lean_ctor_set(v___x_3880_, 1, v___x_3879_);
                    v___x_3881_ = l_Lean_MessageData_ofName(v_mod_3862_);
                    v___x_3882_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3882_, 0, v___x_3880_);
                    lean_ctor_set(v___x_3882_, 1, v___x_3881_);
                    v___x_3883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
                    v___x_3884_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3884_, 0, v___x_3882_);
                    lean_ctor_set(v___x_3884_, 1, v___x_3883_);
                    v___x_3885_ = l_Lean_MessageData_note(v___x_3884_);
                    v___x_3886_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3886_, 0, v_msg_3829_);
                    lean_ctor_set(v___x_3886_, 1, v___x_3885_);
                    if v_isShared_3858_ == 0 {
                        lean_ctor_set_tag(v___x_3857_, 0);
                        lean_ctor_set(v___x_3857_, 0, v___x_3886_);
                        v___x_3888_ = v___x_3857_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
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
    mut v_msg_3892_: *mut LeanObject,
    mut v_declHint_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3896_: *mut LeanObject = core::ptr::null_mut();
    v_res_3896_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_3892_, v_declHint_3893_, v___y_3894_);
    lean_dec(v___y_3894_);
    return v_res_3896_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(
    mut v_msg_3897_: *mut LeanObject,
    mut v_declHint_3898_: *mut LeanObject,
    mut v___y_3899_: *mut LeanObject,
    mut v___y_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_3897_, v_declHint_3898_, v___y_3900_);
                v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
                v_isSharedCheck_3912_ = (!lean_is_exclusive(v___x_3902_)) as u8;
                if v_isSharedCheck_3912_ == 0 {
                    v___x_3905_ = v___x_3902_;
                    v_isShared_3906_ = v_isSharedCheck_3912_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3903_);
                    lean_dec(v___x_3902_);
                    v___x_3905_ = lean_box(0);
                    v_isShared_3906_ = v_isSharedCheck_3912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3907_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3908_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3908_, 0, v___x_3907_);
                lean_ctor_set(v___x_3908_, 1, v_a_3903_);
                if v_isShared_3906_ == 0 {
                    lean_ctor_set(v___x_3905_, 0, v___x_3908_);
                    v___x_3910_ = v___x_3905_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
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
    mut v_msg_3913_: *mut LeanObject,
    mut v_declHint_3914_: *mut LeanObject,
    mut v___y_3915_: *mut LeanObject,
    mut v___y_3916_: *mut LeanObject,
    mut v___y_3917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3918_: *mut LeanObject = core::ptr::null_mut();
    v_res_3918_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_3913_, v_declHint_3914_, v___y_3915_, v___y_3916_);
    lean_dec(v___y_3916_);
    lean_dec_ref(v___y_3915_);
    return v_res_3918_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(
    mut v_ref_3919_: *mut LeanObject,
    mut v_msg_3920_: *mut LeanObject,
    mut v___y_3921_: *mut LeanObject,
    mut v___y_3922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3936_: u8 = 0;
    let mut v_cancelTk_x3f_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3938_: u8 = 0;
    let mut v_inheritedTraceOptions_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3924_ = lean_ctor_get(v___y_3921_, 0);
    v_fileMap_3925_ = lean_ctor_get(v___y_3921_, 1);
    v_options_3926_ = lean_ctor_get(v___y_3921_, 2);
    v_currRecDepth_3927_ = lean_ctor_get(v___y_3921_, 3);
    v_maxRecDepth_3928_ = lean_ctor_get(v___y_3921_, 4);
    v_ref_3929_ = lean_ctor_get(v___y_3921_, 5);
    v_currNamespace_3930_ = lean_ctor_get(v___y_3921_, 6);
    v_openDecls_3931_ = lean_ctor_get(v___y_3921_, 7);
    v_initHeartbeats_3932_ = lean_ctor_get(v___y_3921_, 8);
    v_maxHeartbeats_3933_ = lean_ctor_get(v___y_3921_, 9);
    v_quotContext_3934_ = lean_ctor_get(v___y_3921_, 10);
    v_currMacroScope_3935_ = lean_ctor_get(v___y_3921_, 11);
    v_diag_3936_ = lean_ctor_get_uint8(
        v___y_3921_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3937_ = lean_ctor_get(v___y_3921_, 12);
    v_suppressElabErrors_3938_ = lean_ctor_get_uint8(
        v___y_3921_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3939_ = lean_ctor_get(v___y_3921_, 13);
    v_ref_3940_ = l_Lean_replaceRef(v_ref_3919_, v_ref_3929_);
    lean_inc_ref(v_inheritedTraceOptions_3939_);
    lean_inc(v_cancelTk_x3f_3937_);
    lean_inc(v_currMacroScope_3935_);
    lean_inc(v_quotContext_3934_);
    lean_inc(v_maxHeartbeats_3933_);
    lean_inc(v_initHeartbeats_3932_);
    lean_inc(v_openDecls_3931_);
    lean_inc(v_currNamespace_3930_);
    lean_inc(v_maxRecDepth_3928_);
    lean_inc(v_currRecDepth_3927_);
    lean_inc_ref(v_options_3926_);
    lean_inc_ref(v_fileMap_3925_);
    lean_inc_ref(v_fileName_3924_);
    v___x_3941_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3941_, 0, v_fileName_3924_);
    lean_ctor_set(v___x_3941_, 1, v_fileMap_3925_);
    lean_ctor_set(v___x_3941_, 2, v_options_3926_);
    lean_ctor_set(v___x_3941_, 3, v_currRecDepth_3927_);
    lean_ctor_set(v___x_3941_, 4, v_maxRecDepth_3928_);
    lean_ctor_set(v___x_3941_, 5, v_ref_3940_);
    lean_ctor_set(v___x_3941_, 6, v_currNamespace_3930_);
    lean_ctor_set(v___x_3941_, 7, v_openDecls_3931_);
    lean_ctor_set(v___x_3941_, 8, v_initHeartbeats_3932_);
    lean_ctor_set(v___x_3941_, 9, v_maxHeartbeats_3933_);
    lean_ctor_set(v___x_3941_, 10, v_quotContext_3934_);
    lean_ctor_set(v___x_3941_, 11, v_currMacroScope_3935_);
    lean_ctor_set(v___x_3941_, 12, v_cancelTk_x3f_3937_);
    lean_ctor_set(v___x_3941_, 13, v_inheritedTraceOptions_3939_);
    lean_ctor_set_uint8(
        v___x_3941_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3936_,
    );
    lean_ctor_set_uint8(
        v___x_3941_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3938_,
    );
    v___x_3942_ = l_Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1___redArg(v_msg_3920_, v___x_3941_, v___y_3922_);
    lean_dec_ref_known(v___x_3941_, 14);
    return v___x_3942_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg___boxed(
    mut v_ref_3943_: *mut LeanObject,
    mut v_msg_3944_: *mut LeanObject,
    mut v___y_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
    mut v___y_3947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3948_: *mut LeanObject = core::ptr::null_mut();
    v_res_3948_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_3943_, v_msg_3944_, v___y_3945_, v___y_3946_);
    lean_dec(v___y_3946_);
    lean_dec_ref(v___y_3945_);
    lean_dec(v_ref_3943_);
    return v_res_3948_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(
    mut v_ref_3949_: *mut LeanObject,
    mut v_msg_3950_: *mut LeanObject,
    mut v_declHint_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    v___x_3955_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17(v_msg_3950_, v_declHint_3951_, v___y_3952_, v___y_3953_);
    v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
    lean_inc(v_a_3956_);
    lean_dec_ref(v___x_3955_);
    v___x_3957_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_3949_, v_a_3956_, v___y_3952_, v___y_3953_);
    return v___x_3957_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg___boxed(
    mut v_ref_3958_: *mut LeanObject,
    mut v_msg_3959_: *mut LeanObject,
    mut v_declHint_3960_: *mut LeanObject,
    mut v___y_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
    mut v___y_3963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3964_: *mut LeanObject = core::ptr::null_mut();
    v_res_3964_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_3958_, v_msg_3959_, v_declHint_3960_, v___y_3961_, v___y_3962_);
    lean_dec(v___y_3962_);
    lean_dec_ref(v___y_3961_);
    lean_dec(v_ref_3958_);
    return v_res_3964_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    v___x_3966_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__0;
    v___x_3967_ = l_Lean_stringToMessageData(v___x_3966_);
    return v___x_3967_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(
    mut v_ref_3968_: *mut LeanObject,
    mut v_constName_3969_: *mut LeanObject,
    mut v___y_3970_: *mut LeanObject,
    mut v___y_3971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: u8 = 0;
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    v___x_3973_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___closed__1);
    v___x_3974_ = 0;
    lean_inc(v_constName_3969_);
    v___x_3975_ = l_Lean_MessageData_ofConstName(v_constName_3969_, v___x_3974_);
    v___x_3976_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3976_, 0, v___x_3973_);
    lean_ctor_set(v___x_3976_, 1, v___x_3975_);
    v___x_3977_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3_once),
        _init_l_Lean_Elab_syntaxNodeKindOfAttrParam___closed__3,
    );
    v___x_3978_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3978_, 0, v___x_3976_);
    lean_ctor_set(v___x_3978_, 1, v___x_3977_);
    v___x_3979_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_3968_, v___x_3978_, v_constName_3969_, v___y_3970_, v___y_3971_);
    return v___x_3979_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg___boxed(
    mut v_ref_3980_: *mut LeanObject,
    mut v_constName_3981_: *mut LeanObject,
    mut v___y_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3985_: *mut LeanObject = core::ptr::null_mut();
    v_res_3985_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_3980_, v_constName_3981_, v___y_3982_, v___y_3983_);
    lean_dec(v___y_3983_);
    lean_dec_ref(v___y_3982_);
    lean_dec(v_ref_3980_);
    return v_res_3985_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(
    mut v_constName_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3990_ = lean_ctor_get(v___y_3987_, 5);
    v___x_3991_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_3990_, v_constName_3986_, v___y_3987_, v___y_3988_);
    return v___x_3991_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg___boxed(
    mut v_constName_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3996_: *mut LeanObject = core::ptr::null_mut();
    v_res_3996_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_3992_, v___y_3993_, v___y_3994_);
    lean_dec(v___y_3994_);
    lean_dec_ref(v___y_3993_);
    return v_res_3996_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(
    mut v_constName_3997_: *mut LeanObject,
    mut v___y_3998_: *mut LeanObject,
    mut v___y_3999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: u8 = 0;
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4009_: u8 = 0;
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4001_ = lean_st_ref_get(v___y_3999_);
                v_env_4002_ = lean_ctor_get(v___x_4001_, 0);
                lean_inc_ref(v_env_4002_);
                lean_dec(v___x_4001_);
                v___x_4003_ = 0;
                lean_inc(v_constName_3997_);
                v___x_4004_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_4002_,
                    v_constName_3997_,
                    v___x_4003_,
                );
                if lean_obj_tag(v___x_4004_) == 0 {
                    v___x_4005_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_3997_, v___y_3998_, v___y_3999_);
                    return v___x_4005_;
                } else {
                    lean_dec(v_constName_3997_);
                    v_val_4006_ = lean_ctor_get(v___x_4004_, 0);
                    v_isSharedCheck_4013_ = (!lean_is_exclusive(v___x_4004_)) as u8;
                    if v_isSharedCheck_4013_ == 0 {
                        v___x_4008_ = v___x_4004_;
                        v_isShared_4009_ = v_isSharedCheck_4013_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4006_);
                        lean_dec(v___x_4004_);
                        v___x_4008_ = lean_box(0);
                        v_isShared_4009_ = v_isSharedCheck_4013_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4009_ == 0 {
                    lean_ctor_set_tag(v___x_4008_, 0);
                    v___x_4011_ = v___x_4008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_val_4006_);
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
    mut v_constName_4014_: *mut LeanObject,
    mut v___y_4015_: *mut LeanObject,
    mut v___y_4016_: *mut LeanObject,
    mut v___y_4017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4018_: *mut LeanObject = core::ptr::null_mut();
    v_res_4018_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_4014_, v___y_4015_, v___y_4016_);
    lean_dec(v___y_4016_);
    lean_dec_ref(v___y_4015_);
    return v_res_4018_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(
    mut v_a_4019_: *mut LeanObject,
    mut v_a_4020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4019_) == 0 {
                    v___x_4021_ = l_List_reverse___redArg(v_a_4020_);
                    return v___x_4021_;
                } else {
                    v_head_4022_ = lean_ctor_get(v_a_4019_, 0);
                    v_tail_4023_ = lean_ctor_get(v_a_4019_, 1);
                    v_isSharedCheck_4032_ = (!lean_is_exclusive(v_a_4019_)) as u8;
                    if v_isSharedCheck_4032_ == 0 {
                        v___x_4025_ = v_a_4019_;
                        v_isShared_4026_ = v_isSharedCheck_4032_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4023_);
                        lean_inc(v_head_4022_);
                        lean_dec(v_a_4019_);
                        v___x_4025_ = lean_box(0);
                        v_isShared_4026_ = v_isSharedCheck_4032_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4027_ = l_Lean_mkLevelParam(v_head_4022_);
                if v_isShared_4026_ == 0 {
                    lean_ctor_set(v___x_4025_, 1, v_a_4020_);
                    lean_ctor_set(v___x_4025_, 0, v___x_4027_);
                    v___x_4029_ = v___x_4025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4027_);
                    lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_a_4020_);
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
    mut v_constName_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v_levelParams_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4049_: u8 = 0;
    let mut v_a_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4053_: u8 = 0;
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_4033_);
                v___x_4037_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8(v_constName_4033_, v___y_4034_, v___y_4035_);
                if lean_obj_tag(v___x_4037_) == 0 {
                    v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
                    v_isSharedCheck_4049_ = (!lean_is_exclusive(v___x_4037_)) as u8;
                    if v_isSharedCheck_4049_ == 0 {
                        v___x_4040_ = v___x_4037_;
                        v_isShared_4041_ = v_isSharedCheck_4049_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4038_);
                        lean_dec(v___x_4037_);
                        v___x_4040_ = lean_box(0);
                        v_isShared_4041_ = v_isSharedCheck_4049_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_4033_);
                    v_a_4050_ = lean_ctor_get(v___x_4037_, 0);
                    v_isSharedCheck_4057_ = (!lean_is_exclusive(v___x_4037_)) as u8;
                    if v_isSharedCheck_4057_ == 0 {
                        v___x_4052_ = v___x_4037_;
                        v_isShared_4053_ = v_isSharedCheck_4057_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4050_);
                        lean_dec(v___x_4037_);
                        v___x_4052_ = lean_box(0);
                        v_isShared_4053_ = v_isSharedCheck_4057_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_4042_ = lean_ctor_get(v_a_4038_, 1);
                lean_inc(v_levelParams_4042_);
                lean_dec(v_a_4038_);
                v___x_4043_ = lean_box(0);
                v___x_4044_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__9(v_levelParams_4042_, v___x_4043_);
                v___x_4045_ = l_Lean_mkConst(v_constName_4033_, v___x_4044_);
                if v_isShared_4041_ == 0 {
                    lean_ctor_set(v___x_4040_, 0, v___x_4045_);
                    v___x_4047_ = v___x_4040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4045_);
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
                    v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
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
    mut v_constName_4058_: *mut LeanObject,
    mut v___y_4059_: *mut LeanObject,
    mut v___y_4060_: *mut LeanObject,
    mut v___y_4061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4062_: *mut LeanObject = core::ptr::null_mut();
    v_res_4062_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_constName_4058_, v___y_4059_, v___y_4060_);
    lean_dec(v___y_4060_);
    lean_dec_ref(v___y_4059_);
    return v_res_4062_;
}
pub unsafe fn l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(
    mut v_stx_4063_: *mut LeanObject,
    mut v_n_4064_: *mut LeanObject,
    mut v_expectedType_x3f_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4069_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4(v_n_4064_, v___y_4066_, v___y_4067_);
                if lean_obj_tag(v___x_4069_) == 0 {
                    v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
                    lean_inc(v_a_4070_);
                    lean_dec_ref_known(v___x_4069_, 1);
                    v___x_4071_ = lean_box(0);
                    v___x_4072_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4072_, 0, v___x_4071_);
                    lean_ctor_set(v___x_4072_, 1, v_stx_4063_);
                    v___x_4073_ = l_Lean_LocalContext_empty;
                    v___x_4074_ = 0;
                    v___x_4075_ = lean_alloc_ctor(0, 4, (2) as u32);
                    lean_ctor_set(v___x_4075_, 0, v___x_4072_);
                    lean_ctor_set(v___x_4075_, 1, v___x_4073_);
                    lean_ctor_set(v___x_4075_, 2, v_expectedType_x3f_4065_);
                    lean_ctor_set(v___x_4075_, 3, v_a_4070_);
                    lean_ctor_set_uint8(
                        v___x_4075_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v___x_4074_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4075_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                        v___x_4074_,
                    );
                    v___x_4076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4076_, 0, v___x_4075_);
                    v___x_4077_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5(v___x_4076_, v___y_4066_, v___y_4067_);
                    return v___x_4077_;
                } else {
                    lean_dec(v_expectedType_x3f_4065_);
                    lean_dec(v_stx_4063_);
                    v_a_4078_ = lean_ctor_get(v___x_4069_, 0);
                    v_isSharedCheck_4085_ = (!lean_is_exclusive(v___x_4069_)) as u8;
                    if v_isSharedCheck_4085_ == 0 {
                        v___x_4080_ = v___x_4069_;
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4078_);
                        lean_dec(v___x_4069_);
                        v___x_4080_ = lean_box(0);
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
                    v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
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
    mut v_stx_4086_: *mut LeanObject,
    mut v_n_4087_: *mut LeanObject,
    mut v_expectedType_x3f_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4092_: *mut LeanObject = core::ptr::null_mut();
    v_res_4092_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(
        v_stx_4086_,
        v_n_4087_,
        v_expectedType_x3f_4088_,
        v___y_4089_,
        v___y_4090_,
    );
    lean_dec(v___y_4090_);
    lean_dec_ref(v___y_4089_);
    return v_res_4092_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(
    mut v_keys_4093_: *mut LeanObject,
    mut v_i_4094_: *mut LeanObject,
    mut v_k_4095_: *mut LeanObject,
) -> u8 {
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v_k_x27_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4096_ = lean_array_get_size(v_keys_4093_);
                v___x_4097_ = lean_nat_dec_lt(v_i_4094_, v___x_4096_);
                if v___x_4097_ == 0 {
                    lean_dec(v_i_4094_);
                    return v___x_4097_;
                } else {
                    v_k_x27_4098_ = lean_array_fget_borrowed(v_keys_4093_, v_i_4094_);
                    v___x_4099_ = l_Lean_instBEqExtraModUse_beq(v_k_4095_, v_k_x27_4098_);
                    if v___x_4099_ == 0 {
                        v___x_4100_ = lean_unsigned_to_nat(1);
                        v___x_4101_ = lean_nat_add(v_i_4094_, v___x_4100_);
                        lean_dec(v_i_4094_);
                        v_i_4094_ = v___x_4101_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_4094_);
                        return v___x_4099_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg___boxed(
    mut v_keys_4103_: *mut LeanObject,
    mut v_i_4104_: *mut LeanObject,
    mut v_k_4105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4106_: u8 = 0;
    let mut v_r_4107_: *mut LeanObject = core::ptr::null_mut();
    v_res_4106_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_4103_, v_i_4104_, v_k_4105_);
    lean_dec_ref(v_k_4105_);
    lean_dec_ref(v_keys_4103_);
    v_r_4107_ = lean_box((v_res_4106_) as usize);
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
    v___x_4112_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
    v___x_4113_ = lean_usize_sub(v___x_4112_, v___x_4111_);
    return v___x_4113_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_x_4114_: *mut LeanObject,
    mut v_x_4115_: usize,
    mut v_x_4116_: *mut LeanObject,
) -> u8 {
    let mut v_es_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: usize = 0;
    let mut v___x_4120_: usize = 0;
    let mut v___x_4121_: usize = 0;
    let mut v_j_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v_node_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: usize = 0;
    let mut v___x_4129_: u8 = 0;
    let mut v_ks_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4114_) == 0 {
                    v_es_4117_ = lean_ctor_get(v_x_4114_, 0);
                    v___x_4118_ = lean_box(2);
                    v___x_4119_ = 5usize;
                    v___x_4120_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
                    v___x_4121_ = lean_usize_land(v_x_4115_, v___x_4120_);
                    v_j_4122_ = lean_usize_to_nat(v___x_4121_);
                    v___x_4123_ = lean_array_get_borrowed(v___x_4118_, v_es_4117_, v_j_4122_);
                    lean_dec(v_j_4122_);
                    match lean_obj_tag(v___x_4123_) {
                        0 => {
                            v_key_4124_ = lean_ctor_get(v___x_4123_, 0);
                            v___x_4125_ = l_Lean_instBEqExtraModUse_beq(v_x_4116_, v_key_4124_);
                            return v___x_4125_;
                        }
                        1 => {
                            v_node_4126_ = lean_ctor_get(v___x_4123_, 0);
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
                    v_ks_4130_ = lean_ctor_get(v_x_4114_, 0);
                    v___x_4131_ = lean_unsigned_to_nat(0);
                    v___x_4132_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_ks_4130_, v___x_4131_, v_x_4116_);
                    return v___x_4132_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_4133_: *mut LeanObject,
    mut v_x_4134_: *mut LeanObject,
    mut v_x_4135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6766__boxed_4136_: usize = 0;
    let mut v_res_4137_: u8 = 0;
    let mut v_r_4138_: *mut LeanObject = core::ptr::null_mut();
    v_x_6766__boxed_4136_ = lean_unbox_usize(v_x_4134_);
    lean_dec(v_x_4134_);
    v_res_4137_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4133_, v_x_6766__boxed_4136_, v_x_4135_);
    lean_dec_ref(v_x_4135_);
    lean_dec_ref(v_x_4133_);
    v_r_4138_ = lean_box((v_res_4137_) as usize);
    return v_r_4138_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(
    mut v_x_4139_: *mut LeanObject,
    mut v_x_4140_: *mut LeanObject,
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
    mut v_x_4144_: *mut LeanObject,
    mut v_x_4145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4146_: u8 = 0;
    let mut v_r_4147_: *mut LeanObject = core::ptr::null_mut();
    v_res_4146_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_4144_, v_x_4145_);
    lean_dec_ref(v_x_4145_);
    lean_dec_ref(v_x_4144_);
    v_r_4147_ = lean_box((v_res_4146_) as usize);
    return v_r_4147_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0()
-> f64 {
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: f64 = 0.0;
    v___x_4148_ = lean_unsigned_to_nat(0);
    v___x_4149_ = lean_float_of_nat(v___x_4148_);
    return v___x_4149_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(
    mut v_cls_4153_: *mut LeanObject,
    mut v_msg_4154_: *mut LeanObject,
    mut v___y_4155_: *mut LeanObject,
    mut v___y_4156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4163_: u8 = 0;
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v_tid_4177_: u64 = 0;
    let mut v_traces_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4181_: u8 = 0;
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: f64 = 0.0;
    let mut v___x_4184_: u8 = 0;
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4158_ = lean_ctor_get(v___y_4155_, 5);
                v___x_4159_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSyntaxNodeKindAtNamespaces___at___00Lean_Elab_checkSyntaxNodeKindAtCurrentNamespaces_spec__0_spec__1_spec__2(v_msg_4154_, v___y_4155_, v___y_4156_);
                v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
                v_isSharedCheck_4204_ = (!lean_is_exclusive(v___x_4159_)) as u8;
                if v_isSharedCheck_4204_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    v_isShared_4163_ = v_isSharedCheck_4204_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4160_);
                    lean_dec(v___x_4159_);
                    v___x_4162_ = lean_box(0);
                    v_isShared_4163_ = v_isSharedCheck_4204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4164_ = lean_st_ref_take(v___y_4156_);
                v_traceState_4165_ = lean_ctor_get(v___x_4164_, 4);
                v_env_4166_ = lean_ctor_get(v___x_4164_, 0);
                v_nextMacroScope_4167_ = lean_ctor_get(v___x_4164_, 1);
                v_ngen_4168_ = lean_ctor_get(v___x_4164_, 2);
                v_auxDeclNGen_4169_ = lean_ctor_get(v___x_4164_, 3);
                v_cache_4170_ = lean_ctor_get(v___x_4164_, 5);
                v_messages_4171_ = lean_ctor_get(v___x_4164_, 6);
                v_infoState_4172_ = lean_ctor_get(v___x_4164_, 7);
                v_snapshotTasks_4173_ = lean_ctor_get(v___x_4164_, 8);
                v_isSharedCheck_4203_ = (!lean_is_exclusive(v___x_4164_)) as u8;
                if v_isSharedCheck_4203_ == 0 {
                    v___x_4175_ = v___x_4164_;
                    v_isShared_4176_ = v_isSharedCheck_4203_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4173_);
                    lean_inc(v_infoState_4172_);
                    lean_inc(v_messages_4171_);
                    lean_inc(v_cache_4170_);
                    lean_inc(v_traceState_4165_);
                    lean_inc(v_auxDeclNGen_4169_);
                    lean_inc(v_ngen_4168_);
                    lean_inc(v_nextMacroScope_4167_);
                    lean_inc(v_env_4166_);
                    lean_dec(v___x_4164_);
                    v___x_4175_ = lean_box(0);
                    v_isShared_4176_ = v_isSharedCheck_4203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4177_ = lean_ctor_get_uint64(
                    v_traceState_4165_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4178_ = lean_ctor_get(v_traceState_4165_, 0);
                v_isSharedCheck_4202_ = (!lean_is_exclusive(v_traceState_4165_)) as u8;
                if v_isSharedCheck_4202_ == 0 {
                    v___x_4180_ = v_traceState_4165_;
                    v_isShared_4181_ = v_isSharedCheck_4202_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4178_);
                    lean_dec(v_traceState_4165_);
                    v___x_4180_ = lean_box(0);
                    v_isShared_4181_ = v_isSharedCheck_4202_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4182_ = lean_box(0);
                v___x_4183_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__0);
                v___x_4184_ = 0;
                v___x_4185_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1;
                v___x_4186_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4186_, 0, v_cls_4153_);
                lean_ctor_set(v___x_4186_, 1, v___x_4182_);
                lean_ctor_set(v___x_4186_, 2, v___x_4185_);
                lean_ctor_set_float(
                    v___x_4186_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4183_,
                );
                lean_ctor_set_float(
                    v___x_4186_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4183_,
                );
                lean_ctor_set_uint8(
                    v___x_4186_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4184_,
                );
                v___x_4187_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__2;
                v___x_4188_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4188_, 0, v___x_4186_);
                lean_ctor_set(v___x_4188_, 1, v_a_4160_);
                lean_ctor_set(v___x_4188_, 2, v___x_4187_);
                lean_inc(v_ref_4158_);
                v___x_4189_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4189_, 0, v_ref_4158_);
                lean_ctor_set(v___x_4189_, 1, v___x_4188_);
                v___x_4190_ = l_Lean_PersistentArray_push___redArg(v_traces_4178_, v___x_4189_);
                if v_isShared_4181_ == 0 {
                    lean_ctor_set(v___x_4180_, 0, v___x_4190_);
                    v___x_4192_ = v___x_4180_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4190_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4201_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4177_,
                    );
                    v___x_4192_ = v_reuseFailAlloc_4201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4176_ == 0 {
                    lean_ctor_set(v___x_4175_, 4, v___x_4192_);
                    v___x_4194_ = v___x_4175_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_env_4166_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_nextMacroScope_4167_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 2, v_ngen_4168_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 3, v_auxDeclNGen_4169_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 4, v___x_4192_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 5, v_cache_4170_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 6, v_messages_4171_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 7, v_infoState_4172_);
                    lean_ctor_set(v_reuseFailAlloc_4200_, 8, v_snapshotTasks_4173_);
                    v___x_4194_ = v_reuseFailAlloc_4200_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4195_ = lean_st_ref_set(v___y_4156_, v___x_4194_);
                v___x_4196_ = lean_box(0);
                if v_isShared_4163_ == 0 {
                    lean_ctor_set(v___x_4162_, 0, v___x_4196_);
                    v___x_4198_ = v___x_4162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4196_);
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
    mut v_cls_4205_: *mut LeanObject,
    mut v_msg_4206_: *mut LeanObject,
    mut v___y_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
    mut v___y_4209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4210_: *mut LeanObject = core::ptr::null_mut();
    v_res_4210_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_4205_, v_msg_4206_, v___y_4207_, v___y_4208_);
    lean_dec(v___y_4208_);
    lean_dec_ref(v___y_4207_);
    return v_res_4210_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    v___x_4213_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__1;
    v___x_4214_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__0;
    v___x_4215_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_4214_, v___x_4213_);
    return v___x_4215_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    v___x_4216_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4216_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    v___x_4217_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__3);
    v___x_4218_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4218_, 0, v___x_4217_);
    return v___x_4218_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    v___x_4219_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__4);
    v___x_4220_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4220_, 0, v___x_4219_);
    lean_ctor_set(v___x_4220_, 1, v___x_4219_);
    return v___x_4220_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9()
-> *mut LeanObject {
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    v___x_4225_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__8;
    v___x_4226_ = l_Lean_stringToMessageData(v___x_4225_);
    return v___x_4226_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11()
-> *mut LeanObject {
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    v___x_4228_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__10;
    v___x_4229_ = l_Lean_stringToMessageData(v___x_4228_);
    return v___x_4229_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12()
-> *mut LeanObject {
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2___closed__1;
    v___x_4231_ = l_Lean_stringToMessageData(v___x_4230_);
    return v___x_4231_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15()
-> *mut LeanObject {
    let mut v_cls_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    v_cls_4235_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7;
    v___x_4236_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14;
    v___x_4237_ = l_Lean_Name_append(v___x_4236_, v_cls_4235_);
    return v___x_4237_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17()
-> *mut LeanObject {
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    v___x_4239_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__16;
    v___x_4240_ = l_Lean_stringToMessageData(v___x_4239_);
    return v___x_4240_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19()
-> *mut LeanObject {
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    v___x_4242_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__18;
    v___x_4243_ = l_Lean_stringToMessageData(v___x_4242_);
    return v___x_4243_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(
    mut v_mod_4248_: *mut LeanObject,
    mut v_isMeta_4249_: u8,
    mut v_hint_4250_: *mut LeanObject,
    mut v___y_4251_: *mut LeanObject,
    mut v___y_4252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4256_: u8 = 0;
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v_asyncMode_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4288_: u8 = 0;
    let mut v_unused_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: u8 = 0;
    let mut v_options_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4293_: u8 = 0;
    let mut v_inheritedTraceOptions_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u8 = 0;
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: u8 = 0;
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4254_ = lean_st_ref_get(v___y_4252_);
                v_env_4255_ = lean_ctor_get(v___x_4254_, 0);
                lean_inc_ref(v_env_4255_);
                lean_dec(v___x_4254_);
                v_isExporting_4256_ = lean_ctor_get_uint8(
                    v_env_4255_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_4255_);
                v___x_4257_ = lean_st_ref_get(v___y_4252_);
                v_env_4258_ = lean_ctor_get(v___x_4257_, 0);
                lean_inc_ref(v_env_4258_);
                lean_dec(v___x_4257_);
                v___x_4259_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__2);
                lean_inc(v_mod_4248_);
                v_entry_4260_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_4260_, 0, v_mod_4248_);
                lean_ctor_set_uint8(
                    v_entry_4260_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_4256_,
                );
                lean_ctor_set_uint8(
                    v_entry_4260_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4249_,
                );
                v___x_4261_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_4262_ = lean_box(1);
                v___x_4263_ = lean_box(0);
                v___x_4290_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4259_,
                    v___x_4261_,
                    v_env_4258_,
                    v___x_4262_,
                    v___x_4263_,
                );
                v___x_4291_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v___x_4290_, v_entry_4260_);
                lean_dec(v___x_4290_);
                if v___x_4291_ == 0 {
                    v_options_4292_ = lean_ctor_get(v___y_4251_, 2);
                    v_hasTrace_4293_ = lean_ctor_get_uint8(
                        v_options_4292_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4293_ == 0 {
                        lean_dec(v_hint_4250_);
                        lean_dec(v_mod_4248_);
                        v___y_4265_ = v___y_4252_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4294_ = lean_ctor_get(v___y_4251_, 13);
                        v_cls_4295_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__7;
                        v___x_4315_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__15);
                        v___x_4316_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4294_,
                            v_options_4292_,
                            v___x_4315_,
                        );
                        if v___x_4316_ == 0 {
                            lean_dec(v_hint_4250_);
                            lean_dec(v_mod_4248_);
                            v___y_4265_ = v___y_4252_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4317_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__17);
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
                    lean_dec_ref_known(v_entry_4260_, 1);
                    lean_dec(v_hint_4250_);
                    lean_dec(v_mod_4248_);
                    v___x_4328_ = lean_box(0);
                    v___x_4329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4329_, 0, v___x_4328_);
                    return v___x_4329_;
                }
            }
            1 => {
                v___x_4266_ = lean_st_ref_take(v___y_4265_);
                v_toEnvExtension_4267_ = lean_ctor_get(v___x_4261_, 0);
                v_env_4268_ = lean_ctor_get(v___x_4266_, 0);
                v_nextMacroScope_4269_ = lean_ctor_get(v___x_4266_, 1);
                v_ngen_4270_ = lean_ctor_get(v___x_4266_, 2);
                v_auxDeclNGen_4271_ = lean_ctor_get(v___x_4266_, 3);
                v_traceState_4272_ = lean_ctor_get(v___x_4266_, 4);
                v_messages_4273_ = lean_ctor_get(v___x_4266_, 6);
                v_infoState_4274_ = lean_ctor_get(v___x_4266_, 7);
                v_snapshotTasks_4275_ = lean_ctor_get(v___x_4266_, 8);
                v_isSharedCheck_4288_ = (!lean_is_exclusive(v___x_4266_)) as u8;
                if v_isSharedCheck_4288_ == 0 {
                    v_unused_4289_ = lean_ctor_get(v___x_4266_, 5);
                    lean_dec(v_unused_4289_);
                    v___x_4277_ = v___x_4266_;
                    v_isShared_4278_ = v_isSharedCheck_4288_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4275_);
                    lean_inc(v_infoState_4274_);
                    lean_inc(v_messages_4273_);
                    lean_inc(v_traceState_4272_);
                    lean_inc(v_auxDeclNGen_4271_);
                    lean_inc(v_ngen_4270_);
                    lean_inc(v_nextMacroScope_4269_);
                    lean_inc(v_env_4268_);
                    lean_dec(v___x_4266_);
                    v___x_4277_ = lean_box(0);
                    v_isShared_4278_ = v_isSharedCheck_4288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4279_ = lean_ctor_get(v_toEnvExtension_4267_, 2);
                v___x_4280_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4261_,
                    v_env_4268_,
                    v_entry_4260_,
                    v_asyncMode_4279_,
                    v___x_4263_,
                );
                v___x_4281_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__5);
                if v_isShared_4278_ == 0 {
                    lean_ctor_set(v___x_4277_, 5, v___x_4281_);
                    lean_ctor_set(v___x_4277_, 0, v___x_4280_);
                    v___x_4283_ = v___x_4277_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4280_);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_nextMacroScope_4269_);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 2, v_ngen_4270_);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 3, v_auxDeclNGen_4271_);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 4, v_traceState_4272_);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 5, v___x_4281_);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 6, v_messages_4273_);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 7, v_infoState_4274_);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 8, v_snapshotTasks_4275_);
                    v___x_4283_ = v_reuseFailAlloc_4287_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4284_ = lean_st_ref_set(v___y_4265_, v___x_4283_);
                v___x_4285_ = lean_box(0);
                v___x_4286_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4286_, 0, v___x_4285_);
                return v___x_4286_;
            }
            4 => {
                v___x_4299_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4299_, 0, v___y_4297_);
                lean_ctor_set(v___x_4299_, 1, v___y_4298_);
                v___x_4300_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__2(v_cls_4295_, v___x_4299_, v___y_4251_, v___y_4252_);
                if lean_obj_tag(v___x_4300_) == 0 {
                    lean_dec_ref_known(v___x_4300_, 1);
                    v___y_4265_ = v___y_4252_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_4260_, 1);
                    return v___x_4300_;
                }
            }
            5 => {
                lean_inc_ref(v___y_4303_);
                v___x_4304_ = l_Lean_stringToMessageData(v___y_4303_);
                v___x_4305_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4305_, 0, v___y_4302_);
                lean_ctor_set(v___x_4305_, 1, v___x_4304_);
                v___x_4306_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__9);
                v___x_4307_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4307_, 0, v___x_4305_);
                lean_ctor_set(v___x_4307_, 1, v___x_4306_);
                v___x_4308_ = l_Lean_MessageData_ofName(v_mod_4248_);
                v___x_4309_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4309_, 0, v___x_4307_);
                lean_ctor_set(v___x_4309_, 1, v___x_4308_);
                v___x_4310_ = l_Lean_Name_isAnonymous(v_hint_4250_);
                if v___x_4310_ == 0 {
                    v___x_4311_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__11);
                    v___x_4312_ = l_Lean_MessageData_ofName(v_hint_4250_);
                    v___x_4313_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4313_, 0, v___x_4311_);
                    lean_ctor_set(v___x_4313_, 1, v___x_4312_);
                    v___y_4297_ = v___x_4309_;
                    v___y_4298_ = v___x_4313_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_hint_4250_);
                    v___x_4314_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__12);
                    v___y_4297_ = v___x_4309_;
                    v___y_4298_ = v___x_4314_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v___y_4319_);
                v___x_4320_ = l_Lean_stringToMessageData(v___y_4319_);
                v___x_4321_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4321_, 0, v___x_4317_);
                lean_ctor_set(v___x_4321_, 1, v___x_4320_);
                v___x_4322_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
                v___x_4323_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4323_, 0, v___x_4321_);
                lean_ctor_set(v___x_4323_, 1, v___x_4322_);
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
    mut v_mod_4330_: *mut LeanObject,
    mut v_isMeta_4331_: *mut LeanObject,
    mut v_hint_4332_: *mut LeanObject,
    mut v___y_4333_: *mut LeanObject,
    mut v___y_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_4336_: u8 = 0;
    let mut v_res_4337_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4336_ = (lean_unbox(v_isMeta_4331_) as u8);
    v_res_4337_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_mod_4330_, v_isMeta_boxed_4336_, v_hint_4332_, v___y_4333_, v___y_4334_);
    lean_dec(v___y_4334_);
    lean_dec_ref(v___y_4333_);
    return v_res_4337_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(
    mut v___x_4338_: *mut LeanObject,
    mut v_declName_4339_: *mut LeanObject,
    mut v_as_4340_: *mut LeanObject,
    mut v_sz_4341_: usize,
    mut v_i_4342_: usize,
    mut v_b_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4347_: u8 = 0;
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: usize = 0;
    let mut v___x_4360_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4347_ = lean_usize_dec_lt(v_i_4342_, v_sz_4341_);
                if v___x_4347_ == 0 {
                    lean_dec(v_declName_4339_);
                    v___x_4348_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4348_, 0, v_b_4343_);
                    return v___x_4348_;
                } else {
                    v___x_4349_ = l_Lean_Environment_header(v___x_4338_);
                    v_modules_4350_ = lean_ctor_get(v___x_4349_, 3);
                    lean_inc_ref(v_modules_4350_);
                    lean_dec_ref(v___x_4349_);
                    v___x_4351_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_4352_ = lean_array_uget_borrowed(v_as_4340_, v_i_4342_);
                    v___x_4353_ = lean_array_get(v___x_4351_, v_modules_4350_, v_a_4352_);
                    lean_dec_ref(v_modules_4350_);
                    v_toImport_4354_ = lean_ctor_get(v___x_4353_, 0);
                    lean_inc_ref(v_toImport_4354_);
                    lean_dec(v___x_4353_);
                    v_module_4355_ = lean_ctor_get(v_toImport_4354_, 0);
                    lean_inc(v_module_4355_);
                    lean_dec_ref(v_toImport_4354_);
                    v___x_4356_ = 0;
                    lean_inc(v_declName_4339_);
                    v___x_4357_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_4355_, v___x_4356_, v_declName_4339_, v___y_4344_, v___y_4345_);
                    if lean_obj_tag(v___x_4357_) == 0 {
                        lean_dec_ref_known(v___x_4357_, 1);
                        v___x_4358_ = lean_box(0);
                        v___x_4359_ = 1usize;
                        v___x_4360_ = lean_usize_add(v_i_4342_, v___x_4359_);
                        v_i_4342_ = v___x_4360_;
                        v_b_4343_ = v___x_4358_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_4339_);
                        return v___x_4357_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1___boxed(
    mut v___x_4362_: *mut LeanObject,
    mut v_declName_4363_: *mut LeanObject,
    mut v_as_4364_: *mut LeanObject,
    mut v_sz_4365_: *mut LeanObject,
    mut v_i_4366_: *mut LeanObject,
    mut v_b_4367_: *mut LeanObject,
    mut v___y_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4371_: usize = 0;
    let mut v_i_boxed_4372_: usize = 0;
    let mut v_res_4373_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4371_ = lean_unbox_usize(v_sz_4365_);
    lean_dec(v_sz_4365_);
    v_i_boxed_4372_ = lean_unbox_usize(v_i_4366_);
    lean_dec(v_i_4366_);
    v_res_4373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v___x_4362_, v_declName_4363_, v_as_4364_, v_sz_boxed_4371_, v_i_boxed_4372_, v_b_4367_, v___y_4368_, v___y_4369_);
    lean_dec(v___y_4369_);
    lean_dec_ref(v___y_4368_);
    lean_dec_ref(v_as_4364_);
    lean_dec_ref(v___x_4362_);
    return v_res_4373_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(
    mut v_a_4374_: *mut LeanObject,
    mut v_x_4375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4375_) == 0 {
                    v___x_4376_ = lean_box(0);
                    return v___x_4376_;
                } else {
                    v_key_4377_ = lean_ctor_get(v_x_4375_, 0);
                    v_value_4378_ = lean_ctor_get(v_x_4375_, 1);
                    v_tail_4379_ = lean_ctor_get(v_x_4375_, 2);
                    v___x_4380_ = lean_name_eq(v_key_4377_, v_a_4374_);
                    if v___x_4380_ == 0 {
                        v_x_4375_ = v_tail_4379_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_4378_);
                        v___x_4382_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4382_, 0, v_value_4378_);
                        return v___x_4382_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_a_4383_: *mut LeanObject,
    mut v_x_4384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4385_: *mut LeanObject = core::ptr::null_mut();
    v_res_4385_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_4383_, v_x_4384_);
    lean_dec(v_x_4384_);
    lean_dec(v_a_4383_);
    return v_res_4385_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u64 = 0;
    v___x_4386_ = lean_unsigned_to_nat(1723);
    v___x_4387_ = lean_uint64_of_nat(v___x_4386_);
    return v___x_4387_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(
    mut v_m_4388_: *mut LeanObject,
    mut v_a_4389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: u64 = 0;
    let mut v_hash_4408_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4390_ = lean_ctor_get(v_m_4388_, 1);
                v___x_4391_ = lean_array_get_size(v_buckets_4390_);
                if lean_obj_tag(v_a_4389_) == 0 {
                    v___x_4407_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg___closed__0);
                    v___y_4393_ = v___x_4407_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4408_ = lean_ctor_get_uint64(
                        v_a_4389_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_4409_: *mut LeanObject,
    mut v_a_4410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4411_: *mut LeanObject = core::ptr::null_mut();
    v_res_4411_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_4409_, v_a_4410_);
    lean_dec(v_a_4410_);
    lean_dec_ref(v_m_4409_);
    return v_res_4411_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    v___x_4414_ =
        l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__1;
    v___x_4415_ =
        l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__0;
    v___x_4416_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_4415_, v___x_4414_);
    return v___x_4416_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(
    mut v_declName_4419_: *mut LeanObject,
    mut v_isMeta_4420_: u8,
    mut v___y_4421_: *mut LeanObject,
    mut v___y_4422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4432_: usize = 0;
    let mut v___x_4433_: usize = 0;
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4441_: u8 = 0;
    let mut v_unused_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4454_: u8 = 0;
    let mut v_toImport_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v___x_4466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4424_ = lean_st_ref_get(v___y_4422_);
                v_env_4428_ = lean_ctor_get(v___x_4424_, 0);
                lean_inc_ref(v_env_4428_);
                lean_dec(v___x_4424_);
                v___x_4443_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4428_, v_declName_4419_);
                if lean_obj_tag(v___x_4443_) == 0 {
                    lean_dec_ref(v_env_4428_);
                    lean_dec(v_declName_4419_);
                    state = 1;
                    continue;
                } else {
                    v_val_4444_ = lean_ctor_get(v___x_4443_, 0);
                    lean_inc(v_val_4444_);
                    lean_dec_ref_known(v___x_4443_, 1);
                    v___x_4445_ = l_Lean_Environment_header(v_env_4428_);
                    v_modules_4446_ = lean_ctor_get(v___x_4445_, 3);
                    lean_inc_ref(v_modules_4446_);
                    lean_dec_ref(v___x_4445_);
                    v___x_4447_ = lean_array_get_size(v_modules_4446_);
                    v___x_4448_ = lean_nat_dec_lt(v_val_4444_, v___x_4447_);
                    if v___x_4448_ == 0 {
                        lean_dec_ref(v_modules_4446_);
                        lean_dec(v_val_4444_);
                        lean_dec_ref(v_env_4428_);
                        lean_dec(v_declName_4419_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4449_ = lean_st_ref_get(v___y_4422_);
                        v_env_4450_ = lean_ctor_get(v___x_4449_, 0);
                        lean_inc_ref(v_env_4450_);
                        lean_dec(v___x_4449_);
                        v___x_4451_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__2);
                        v___x_4452_ = lean_array_fget(v_modules_4446_, v_val_4444_);
                        lean_dec(v_val_4444_);
                        lean_dec_ref(v_modules_4446_);
                        if v_isMeta_4420_ == 0 {
                            lean_dec_ref(v_env_4450_);
                            v___y_4454_ = v_isMeta_4420_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_4419_);
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
                v___x_4426_ = lean_box(0);
                v___x_4427_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4427_, 0, v___x_4426_);
                return v___x_4427_;
            }
            2 => {
                v___x_4431_ = lean_box(0);
                v_sz_4432_ = lean_array_size(v___y_4430_);
                v___x_4433_ = 0usize;
                v___x_4434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__1(v_env_4428_, v_declName_4419_, v___y_4430_, v_sz_4432_, v___x_4433_, v___x_4431_, v___y_4421_, v___y_4422_);
                lean_dec_ref(v___y_4430_);
                lean_dec_ref(v_env_4428_);
                if lean_obj_tag(v___x_4434_) == 0 {
                    v_isSharedCheck_4441_ = (!lean_is_exclusive(v___x_4434_)) as u8;
                    if v_isSharedCheck_4441_ == 0 {
                        v_unused_4442_ = lean_ctor_get(v___x_4434_, 0);
                        lean_dec(v_unused_4442_);
                        v___x_4436_ = v___x_4434_;
                        v_isShared_4437_ = v_isSharedCheck_4441_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_4434_);
                        v___x_4436_ = lean_box(0);
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
                    lean_ctor_set(v___x_4436_, 0, v___x_4431_);
                    v___x_4439_ = v___x_4436_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4431_);
                    v___x_4439_ = v_reuseFailAlloc_4440_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4439_;
            }
            5 => {
                v_toImport_4455_ = lean_ctor_get(v___x_4452_, 0);
                lean_inc_ref(v_toImport_4455_);
                lean_dec(v___x_4452_);
                v_module_4456_ = lean_ctor_get(v_toImport_4455_, 0);
                lean_inc(v_module_4456_);
                lean_dec_ref(v_toImport_4455_);
                lean_inc(v_declName_4419_);
                v___x_4457_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0(v_module_4456_, v___y_4454_, v_declName_4419_, v___y_4421_, v___y_4422_);
                if lean_obj_tag(v___x_4457_) == 0 {
                    lean_dec_ref_known(v___x_4457_, 1);
                    v___x_4458_ = l_Lean_indirectModUseExt;
                    v___x_4459_ = lean_box(1);
                    v___x_4460_ = lean_box(0);
                    lean_inc_ref(v_env_4428_);
                    v___x_4461_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4451_,
                        v___x_4458_,
                        v_env_4428_,
                        v___x_4459_,
                        v___x_4460_,
                    );
                    v___x_4462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v___x_4461_, v_declName_4419_);
                    lean_dec(v___x_4461_);
                    if lean_obj_tag(v___x_4462_) == 0 {
                        v___x_4463_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___closed__3;
                        v___y_4430_ = v___x_4463_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4464_ = lean_ctor_get(v___x_4462_, 0);
                        lean_inc(v_val_4464_);
                        lean_dec_ref_known(v___x_4462_, 1);
                        v___y_4430_ = v_val_4464_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_4428_);
                    lean_dec(v_declName_4419_);
                    return v___x_4457_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0___boxed(
    mut v_declName_4467_: *mut LeanObject,
    mut v_isMeta_4468_: *mut LeanObject,
    mut v___y_4469_: *mut LeanObject,
    mut v___y_4470_: *mut LeanObject,
    mut v___y_4471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_4472_: u8 = 0;
    let mut v_res_4473_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4472_ = (lean_unbox(v_isMeta_4468_) as u8);
    v_res_4473_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(
        v_declName_4467_,
        v_isMeta_boxed_4472_,
        v___y_4469_,
        v___y_4470_,
    );
    lean_dec(v___y_4470_);
    lean_dec_ref(v___y_4469_);
    return v_res_4473_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg___lam__1(
    mut v_parserNamespace_4474_: *mut LeanObject,
    mut v_x_4475_: u8,
    mut v_stx_4476_: *mut LeanObject,
    mut v___y_4477_: *mut LeanObject,
    mut v___y_4478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4484_: u8 = 0;
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: u8 = 0;
    let mut v___x_4488_: u8 = 0;
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: u8 = 0;
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_4499_: u8 = 0;
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_unused_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_unused_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4528_: u8 = 0;
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v_isSharedCheck_4533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_stx_4476_);
                v___x_4480_ = l_Lean_Elab_syntaxNodeKindOfAttrParam(
                    v_parserNamespace_4474_,
                    v_stx_4476_,
                    v___y_4477_,
                    v___y_4478_,
                );
                if lean_obj_tag(v___x_4480_) == 0 {
                    v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
                    v_isSharedCheck_4533_ = (!lean_is_exclusive(v___x_4480_)) as u8;
                    if v_isSharedCheck_4533_ == 0 {
                        v___x_4483_ = v___x_4480_;
                        v_isShared_4484_ = v_isSharedCheck_4533_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4481_);
                        lean_dec(v___x_4480_);
                        v___x_4483_ = lean_box(0);
                        v_isShared_4484_ = v_isSharedCheck_4533_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_stx_4476_);
                    return v___x_4480_;
                }
            }
            1 => {
                v___x_4485_ = lean_st_ref_get(v___y_4478_);
                v_env_4486_ = lean_ctor_get(v___x_4485_, 0);
                lean_inc_ref(v_env_4486_);
                lean_dec(v___x_4485_);
                v___x_4487_ = 1;
                lean_inc(v_a_4481_);
                v___x_4488_ = l_Lean_Environment_contains(v_env_4486_, v_a_4481_, v___x_4487_);
                if v___x_4488_ == 0 {
                    lean_dec(v_stx_4476_);
                    if v_isShared_4484_ == 0 {
                        v___x_4490_ = v___x_4483_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4481_);
                        v___x_4490_ = v_reuseFailAlloc_4491_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4483_);
                    v___x_4492_ = 0;
                    lean_inc(v_a_4481_);
                    v___x_4493_ =
                        l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0(
                            v_a_4481_,
                            v___x_4492_,
                            v___y_4477_,
                            v___y_4478_,
                        );
                    if lean_obj_tag(v___x_4493_) == 0 {
                        v_isSharedCheck_4523_ = (!lean_is_exclusive(v___x_4493_)) as u8;
                        if v_isSharedCheck_4523_ == 0 {
                            v_unused_4524_ = lean_ctor_get(v___x_4493_, 0);
                            lean_dec(v_unused_4524_);
                            v___x_4495_ = v___x_4493_;
                            v_isShared_4496_ = v_isSharedCheck_4523_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_4493_);
                            v___x_4495_ = lean_box(0);
                            v_isShared_4496_ = v_isSharedCheck_4523_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4481_);
                        lean_dec(v_stx_4476_);
                        v_a_4525_ = lean_ctor_get(v___x_4493_, 0);
                        v_isSharedCheck_4532_ = (!lean_is_exclusive(v___x_4493_)) as u8;
                        if v_isSharedCheck_4532_ == 0 {
                            v___x_4527_ = v___x_4493_;
                            v_isShared_4528_ = v_isSharedCheck_4532_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_4525_);
                            lean_dec(v___x_4493_);
                            v___x_4527_ = lean_box(0);
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
                v_infoState_4498_ = lean_ctor_get(v___x_4497_, 7);
                lean_inc_ref(v_infoState_4498_);
                lean_dec(v___x_4497_);
                v_enabled_4499_ = lean_ctor_get_uint8(
                    v_infoState_4498_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_4498_);
                if v_enabled_4499_ == 0 {
                    lean_dec(v_stx_4476_);
                    if v_isShared_4496_ == 0 {
                        lean_ctor_set(v___x_4495_, 0, v_a_4481_);
                        v___x_4501_ = v___x_4495_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4481_);
                        v___x_4501_ = v_reuseFailAlloc_4502_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4495_);
                    v___x_4503_ = lean_unsigned_to_nat(1);
                    v___x_4504_ = l_Lean_Syntax_getArg(v_stx_4476_, v___x_4503_);
                    lean_dec(v_stx_4476_);
                    v___x_4505_ = lean_box(0);
                    lean_inc(v_a_4481_);
                    v___x_4506_ =
                        l_Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1(
                            v___x_4504_,
                            v_a_4481_,
                            v___x_4505_,
                            v___y_4477_,
                            v___y_4478_,
                        );
                    if lean_obj_tag(v___x_4506_) == 0 {
                        v_isSharedCheck_4513_ = (!lean_is_exclusive(v___x_4506_)) as u8;
                        if v_isSharedCheck_4513_ == 0 {
                            v_unused_4514_ = lean_ctor_get(v___x_4506_, 0);
                            lean_dec(v_unused_4514_);
                            v___x_4508_ = v___x_4506_;
                            v_isShared_4509_ = v_isSharedCheck_4513_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_4506_);
                            v___x_4508_ = lean_box(0);
                            v_isShared_4509_ = v_isSharedCheck_4513_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4481_);
                        v_a_4515_ = lean_ctor_get(v___x_4506_, 0);
                        v_isSharedCheck_4522_ = (!lean_is_exclusive(v___x_4506_)) as u8;
                        if v_isSharedCheck_4522_ == 0 {
                            v___x_4517_ = v___x_4506_;
                            v_isShared_4518_ = v_isSharedCheck_4522_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_4515_);
                            lean_dec(v___x_4506_);
                            v___x_4517_ = lean_box(0);
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
                    lean_ctor_set(v___x_4508_, 0, v_a_4481_);
                    v___x_4511_ = v___x_4508_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4481_);
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
                    v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
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
                    v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4525_);
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
    mut v_parserNamespace_4534_: *mut LeanObject,
    mut v_x_4535_: *mut LeanObject,
    mut v_stx_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
    mut v___y_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7364__boxed_4540_: u8 = 0;
    let mut v_res_4541_: *mut LeanObject = core::ptr::null_mut();
    v_x_7364__boxed_4540_ = (lean_unbox(v_x_4535_) as u8);
    v_res_4541_ = l_Lean_Elab_mkElabAttribute___redArg___lam__1(
        v_parserNamespace_4534_,
        v_x_7364__boxed_4540_,
        v_stx_4536_,
        v___y_4537_,
        v___y_4538_,
    );
    lean_dec(v___y_4538_);
    lean_dec_ref(v___y_4537_);
    return v_res_4541_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg(
    mut v_attrBuiltinName_4544_: *mut LeanObject,
    mut v_attrName_4545_: *mut LeanObject,
    mut v_parserNamespace_4546_: *mut LeanObject,
    mut v_typeName_4547_: *mut LeanObject,
    mut v_kind_4548_: *mut LeanObject,
    mut v_attrDeclName_4549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    v___f_4551_ = l_Lean_Elab_mkElabAttribute___redArg___closed__0;
    v___f_4552_ = lean_alloc_closure(
        l_Lean_Elab_mkElabAttribute___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_4552_, 0, v_parserNamespace_4546_);
    v___x_4553_ = l_Lean_Elab_mkElabAttribute___redArg___closed__1;
    v___x_4554_ = lean_string_append(v_kind_4548_, v___x_4553_);
    v___x_4555_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4555_, 0, v_attrBuiltinName_4544_);
    lean_ctor_set(v___x_4555_, 1, v_attrName_4545_);
    lean_ctor_set(v___x_4555_, 2, v___x_4554_);
    lean_ctor_set(v___x_4555_, 3, v_typeName_4547_);
    lean_ctor_set(v___x_4555_, 4, v___f_4552_);
    lean_ctor_set(v___x_4555_, 5, v___f_4551_);
    v___x_4556_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4555_, v_attrDeclName_4549_);
    return v___x_4556_;
}
pub unsafe fn l_Lean_Elab_mkElabAttribute___redArg___boxed(
    mut v_attrBuiltinName_4557_: *mut LeanObject,
    mut v_attrName_4558_: *mut LeanObject,
    mut v_parserNamespace_4559_: *mut LeanObject,
    mut v_typeName_4560_: *mut LeanObject,
    mut v_kind_4561_: *mut LeanObject,
    mut v_attrDeclName_4562_: *mut LeanObject,
    mut v_a_4563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4564_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b3_4565_: *mut LeanObject,
    mut v_attrBuiltinName_4566_: *mut LeanObject,
    mut v_attrName_4567_: *mut LeanObject,
    mut v_parserNamespace_4568_: *mut LeanObject,
    mut v_typeName_4569_: *mut LeanObject,
    mut v_kind_4570_: *mut LeanObject,
    mut v_attrDeclName_4571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b3_4574_: *mut LeanObject,
    mut v_attrBuiltinName_4575_: *mut LeanObject,
    mut v_attrName_4576_: *mut LeanObject,
    mut v_parserNamespace_4577_: *mut LeanObject,
    mut v_typeName_4578_: *mut LeanObject,
    mut v_kind_4579_: *mut LeanObject,
    mut v_attrDeclName_4580_: *mut LeanObject,
    mut v_a_4581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4582_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b2_4583_: *mut LeanObject,
    mut v_m_4584_: *mut LeanObject,
    mut v_a_4585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    v___x_4586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___redArg(v_m_4584_, v_a_4585_);
    return v___x_4586_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2___boxed(
    mut v_00_u03b2_4587_: *mut LeanObject,
    mut v_m_4588_: *mut LeanObject,
    mut v_a_4589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4590_: *mut LeanObject = core::ptr::null_mut();
    v_res_4590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2(v_00_u03b2_4587_, v_m_4588_, v_a_4589_);
    lean_dec(v_a_4589_);
    lean_dec_ref(v_m_4588_);
    return v_res_4590_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(
    mut v_t_4591_: *mut LeanObject,
    mut v___y_4592_: *mut LeanObject,
    mut v___y_4593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    v___x_4595_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___redArg(v_t_4591_, v___y_4593_);
    return v___x_4595_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11___boxed(
    mut v_t_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4600_: *mut LeanObject = core::ptr::null_mut();
    v_res_4600_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__5_spec__11(v_t_4596_, v___y_4597_, v___y_4598_);
    lean_dec(v___y_4598_);
    lean_dec_ref(v___y_4597_);
    return v_res_4600_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4601_: *mut LeanObject,
    mut v_x_4602_: *mut LeanObject,
    mut v_x_4603_: *mut LeanObject,
) -> u8 {
    let mut v___x_4604_: u8 = 0;
    v___x_4604_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___redArg(v_x_4602_, v_x_4603_);
    return v___x_4604_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4605_: *mut LeanObject,
    mut v_x_4606_: *mut LeanObject,
    mut v_x_4607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4608_: u8 = 0;
    let mut v_r_4609_: *mut LeanObject = core::ptr::null_mut();
    v_res_4608_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1(v_00_u03b2_4605_, v_x_4606_, v_x_4607_);
    lean_dec_ref(v_x_4607_);
    lean_dec_ref(v_x_4606_);
    v_r_4609_ = lean_box((v_res_4608_) as usize);
    return v_r_4609_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(
    mut v_00_u03b2_4610_: *mut LeanObject,
    mut v_a_4611_: *mut LeanObject,
    mut v_x_4612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    v___x_4613_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___redArg(v_a_4611_, v_x_4612_);
    return v___x_4613_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b2_4614_: *mut LeanObject,
    mut v_a_4615_: *mut LeanObject,
    mut v_x_4616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4617_: *mut LeanObject = core::ptr::null_mut();
    v_res_4617_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__2_spec__5(v_00_u03b2_4614_, v_a_4615_, v_x_4616_);
    lean_dec(v_x_4616_);
    lean_dec(v_a_4615_);
    return v_res_4617_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4618_: *mut LeanObject,
    mut v_x_4619_: *mut LeanObject,
    mut v_x_4620_: usize,
    mut v_x_4621_: *mut LeanObject,
) -> u8 {
    let mut v___x_4622_: u8 = 0;
    v___x_4622_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4619_, v_x_4620_, v_x_4621_);
    return v___x_4622_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4623_: *mut LeanObject,
    mut v_x_4624_: *mut LeanObject,
    mut v_x_4625_: *mut LeanObject,
    mut v_x_4626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7534__boxed_4627_: usize = 0;
    let mut v_res_4628_: u8 = 0;
    let mut v_r_4629_: *mut LeanObject = core::ptr::null_mut();
    v_x_7534__boxed_4627_ = lean_unbox_usize(v_x_4625_);
    lean_dec(v_x_4625_);
    v_res_4628_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4623_, v_x_4624_, v_x_7534__boxed_4627_, v_x_4626_);
    lean_dec_ref(v_x_4626_);
    lean_dec_ref(v_x_4624_);
    v_r_4629_ = lean_box((v_res_4628_) as usize);
    return v_r_4629_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(
    mut v_00_u03b1_4630_: *mut LeanObject,
    mut v_constName_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
    mut v___y_4633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    v___x_4635_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___redArg(v_constName_4631_, v___y_4632_, v___y_4633_);
    return v___x_4635_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10___boxed(
    mut v_00_u03b1_4636_: *mut LeanObject,
    mut v_constName_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
    mut v___y_4639_: *mut LeanObject,
    mut v___y_4640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4641_: *mut LeanObject = core::ptr::null_mut();
    v_res_4641_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10(v_00_u03b1_4636_, v_constName_4637_, v___y_4638_, v___y_4639_);
    lean_dec(v___y_4639_);
    lean_dec_ref(v___y_4638_);
    return v_res_4641_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(
    mut v_00_u03b2_4642_: *mut LeanObject,
    mut v_keys_4643_: *mut LeanObject,
    mut v_vals_4644_: *mut LeanObject,
    mut v_heq_4645_: *mut LeanObject,
    mut v_i_4646_: *mut LeanObject,
    mut v_k_4647_: *mut LeanObject,
) -> u8 {
    let mut v___x_4648_: u8 = 0;
    v___x_4648_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___redArg(v_keys_4643_, v_i_4646_, v_k_4647_);
    return v___x_4648_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9___boxed(
    mut v_00_u03b2_4649_: *mut LeanObject,
    mut v_keys_4650_: *mut LeanObject,
    mut v_vals_4651_: *mut LeanObject,
    mut v_heq_4652_: *mut LeanObject,
    mut v_i_4653_: *mut LeanObject,
    mut v_k_4654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4655_: u8 = 0;
    let mut v_r_4656_: *mut LeanObject = core::ptr::null_mut();
    v_res_4655_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0_spec__1_spec__3_spec__9(v_00_u03b2_4649_, v_keys_4650_, v_vals_4651_, v_heq_4652_, v_i_4653_, v_k_4654_);
    lean_dec_ref(v_k_4654_);
    lean_dec_ref(v_vals_4651_);
    lean_dec_ref(v_keys_4650_);
    v_r_4656_ = lean_box((v_res_4655_) as usize);
    return v_r_4656_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(
    mut v_00_u03b1_4657_: *mut LeanObject,
    mut v_ref_4658_: *mut LeanObject,
    mut v_constName_4659_: *mut LeanObject,
    mut v___y_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    v___x_4663_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___redArg(v_ref_4658_, v_constName_4659_, v___y_4660_, v___y_4661_);
    return v___x_4663_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14___boxed(
    mut v_00_u03b1_4664_: *mut LeanObject,
    mut v_ref_4665_: *mut LeanObject,
    mut v_constName_4666_: *mut LeanObject,
    mut v___y_4667_: *mut LeanObject,
    mut v___y_4668_: *mut LeanObject,
    mut v___y_4669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4670_: *mut LeanObject = core::ptr::null_mut();
    v_res_4670_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14(v_00_u03b1_4664_, v_ref_4665_, v_constName_4666_, v___y_4667_, v___y_4668_);
    lean_dec(v___y_4668_);
    lean_dec_ref(v___y_4667_);
    lean_dec(v_ref_4665_);
    return v_res_4670_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(
    mut v_00_u03b1_4671_: *mut LeanObject,
    mut v_ref_4672_: *mut LeanObject,
    mut v_msg_4673_: *mut LeanObject,
    mut v_declHint_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    v___x_4678_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___redArg(v_ref_4672_, v_msg_4673_, v_declHint_4674_, v___y_4675_, v___y_4676_);
    return v___x_4678_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16___boxed(
    mut v_00_u03b1_4679_: *mut LeanObject,
    mut v_ref_4680_: *mut LeanObject,
    mut v_msg_4681_: *mut LeanObject,
    mut v_declHint_4682_: *mut LeanObject,
    mut v___y_4683_: *mut LeanObject,
    mut v___y_4684_: *mut LeanObject,
    mut v___y_4685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4686_: *mut LeanObject = core::ptr::null_mut();
    v_res_4686_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16(v_00_u03b1_4679_, v_ref_4680_, v_msg_4681_, v_declHint_4682_, v___y_4683_, v___y_4684_);
    lean_dec(v___y_4684_);
    lean_dec_ref(v___y_4683_);
    lean_dec(v_ref_4680_);
    return v_res_4686_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(
    mut v_msg_4687_: *mut LeanObject,
    mut v_declHint_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    v___x_4692_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_4687_, v_declHint_4688_, v___y_4690_);
    return v___x_4692_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18___boxed(
    mut v_msg_4693_: *mut LeanObject,
    mut v_declHint_4694_: *mut LeanObject,
    mut v___y_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
    mut v___y_4697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4698_: *mut LeanObject = core::ptr::null_mut();
    v_res_4698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__17_spec__18(v_msg_4693_, v_declHint_4694_, v___y_4695_, v___y_4696_);
    lean_dec(v___y_4696_);
    lean_dec_ref(v___y_4695_);
    return v_res_4698_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(
    mut v_00_u03b1_4699_: *mut LeanObject,
    mut v_ref_4700_: *mut LeanObject,
    mut v_msg_4701_: *mut LeanObject,
    mut v___y_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    v___x_4705_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___redArg(v_ref_4700_, v_msg_4701_, v___y_4702_, v___y_4703_);
    return v___x_4705_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18___boxed(
    mut v_00_u03b1_4706_: *mut LeanObject,
    mut v_ref_4707_: *mut LeanObject,
    mut v_msg_4708_: *mut LeanObject,
    mut v___y_4709_: *mut LeanObject,
    mut v___y_4710_: *mut LeanObject,
    mut v___y_4711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4712_: *mut LeanObject = core::ptr::null_mut();
    v_res_4712_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_mkElabAttribute_spec__1_spec__4_spec__8_spec__10_spec__14_spec__16_spec__18(v_00_u03b1_4706_, v_ref_4707_, v_msg_4708_, v___y_4709_, v___y_4710_);
    lean_dec(v___y_4710_);
    lean_dec_ref(v___y_4709_);
    lean_dec(v_ref_4707_);
    return v_res_4712_;
}
pub unsafe fn l_Lean_Elab_mkMacroAttributeUnsafe(
    mut v_ref_4723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    v___x_4725_ = l_Lean_Elab_mkMacroAttributeUnsafe___closed__1;
    v___x_4726_ = l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
    v___x_4727_ = l_Lean_Elab_mkMacroAttributeUnsafe___closed__3;
    v___x_4728_ = lean_box(0);
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
    mut v_ref_4731_: *mut LeanObject,
    mut v_a_4732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4733_: *mut LeanObject = core::ptr::null_mut();
    v_res_4733_ = l_Lean_Elab_mkMacroAttributeUnsafe(v_ref_4731_);
    return v_res_4733_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    v___x_4740_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_;
    v___x_4741_ = l_Lean_Elab_mkMacroAttributeUnsafe(v___x_4740_);
    return v___x_4741_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2____boxed(
    mut v_a_4742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4743_: *mut LeanObject = core::ptr::null_mut();
    v_res_4743_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
    return v_res_4743_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1()
-> *mut LeanObject {
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    v___x_4746_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_;
    v___x_4747_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___closed__0;
    v___x_4748_ = l_Lean_addBuiltinDocString(v___x_4746_, v___x_4747_);
    return v___x_4748_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1___boxed(
    mut v_a_4749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4750_: *mut LeanObject = core::ptr::null_mut();
    v_res_4750_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
    return v_res_4750_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3()
-> *mut LeanObject {
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    v___x_4777_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_;
    v___x_4778_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___closed__6;
    v___x_4779_ = l_Lean_addBuiltinDeclarationRanges(v___x_4777_, v___x_4778_);
    return v___x_4779_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3___boxed(
    mut v_a_4780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4781_: *mut LeanObject = core::ptr::null_mut();
    v_res_4781_ = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
    return v_res_4781_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(
    mut v_toOLeanEntry_4782_: *mut LeanObject,
    mut v_a_4783_: *mut LeanObject,
    mut v_____r_4784_: *mut LeanObject,
    mut v___y_4785_: *mut LeanObject,
    mut v___y_4786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4790_: u8 = 0;
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4798_: u8 = 0;
    let mut v_unused_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_4787_ = lean_ctor_get(v_toOLeanEntry_4782_, 1);
                v_isSharedCheck_4798_ = (!lean_is_exclusive(v_toOLeanEntry_4782_)) as u8;
                if v_isSharedCheck_4798_ == 0 {
                    v_unused_4799_ = lean_ctor_get(v_toOLeanEntry_4782_, 0);
                    lean_dec(v_unused_4799_);
                    v___x_4789_ = v_toOLeanEntry_4782_;
                    v_isShared_4790_ = v_isSharedCheck_4798_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_declName_4787_);
                    lean_dec(v_toOLeanEntry_4782_);
                    v___x_4789_ = lean_box(0);
                    v_isShared_4790_ = v_isSharedCheck_4798_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4791_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4791_, 0, v_a_4783_);
                if v_isShared_4790_ == 0 {
                    lean_ctor_set(v___x_4789_, 1, v___x_4791_);
                    lean_ctor_set(v___x_4789_, 0, v_declName_4787_);
                    v___x_4793_ = v___x_4789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_declName_4787_);
                    lean_ctor_set(v_reuseFailAlloc_4797_, 1, v___x_4791_);
                    v___x_4793_ = v_reuseFailAlloc_4797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4794_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4794_, 0, v___x_4793_);
                v___x_4795_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4795_, 0, v___x_4794_);
                v___x_4796_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4796_, 0, v___x_4795_);
                lean_ctor_set(v___x_4796_, 1, v___y_4786_);
                return v___x_4796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0___boxed(
    mut v_toOLeanEntry_4800_: *mut LeanObject,
    mut v_a_4801_: *mut LeanObject,
    mut v_____r_4802_: *mut LeanObject,
    mut v___y_4803_: *mut LeanObject,
    mut v___y_4804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4805_: *mut LeanObject = core::ptr::null_mut();
    v_res_4805_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(
            v_toOLeanEntry_4800_,
            v_a_4801_,
            v_____r_4802_,
            v___y_4803_,
            v___y_4804_,
        );
    lean_dec_ref(v___y_4803_);
    return v_res_4805_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(
    mut v_stx_4809_: *mut LeanObject,
    mut v_as_x27_4810_: *mut LeanObject,
    mut v_b_4811_: *mut LeanObject,
    mut v___y_4812_: *mut LeanObject,
    mut v___y_4813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toOLeanEntry_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isBuiltin_4818_: u8 = 0;
    let mut v_value_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroScope_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v_methods_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v_macroScope_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4870_: u8 = 0;
    let mut v_declName_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_isSharedCheck_4880_: u8 = 0;
    let mut v_a_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4810_) == 0 {
                    lean_dec(v_stx_4809_);
                    v___x_4814_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4814_, 0, v_b_4811_);
                    lean_ctor_set(v___x_4814_, 1, v___y_4813_);
                    return v___x_4814_;
                } else {
                    lean_dec_ref(v_b_4811_);
                    v_head_4815_ = lean_ctor_get(v_as_x27_4810_, 0);
                    v_tail_4816_ = lean_ctor_get(v_as_x27_4810_, 1);
                    v_toOLeanEntry_4817_ = lean_ctor_get(v_head_4815_, 0);
                    v_isBuiltin_4818_ = lean_ctor_get_uint8(
                        v_head_4815_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_value_4819_ = lean_ctor_get(v_head_4815_, 1);
                    v_macroScope_4820_ = lean_ctor_get(v___y_4813_, 0);
                    v_traceMsgs_4821_ = lean_ctor_get(v___y_4813_, 1);
                    v_expandedMacroDecls_4822_ = lean_ctor_get(v___y_4813_, 2);
                    v_isSharedCheck_4887_ = (!lean_is_exclusive(v___y_4813_)) as u8;
                    if v_isSharedCheck_4887_ == 0 {
                        v___x_4824_ = v___y_4813_;
                        v_isShared_4825_ = v_isSharedCheck_4887_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_expandedMacroDecls_4822_);
                        lean_inc(v_traceMsgs_4821_);
                        lean_inc(v_macroScope_4820_);
                        lean_dec(v___y_4813_);
                        v___x_4824_ = lean_box(0);
                        v_isShared_4825_ = v_isSharedCheck_4887_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_methods_4826_ = lean_ctor_get(v___y_4812_, 0);
                v_quotContext_4827_ = lean_ctor_get(v___y_4812_, 1);
                v_currRecDepth_4828_ = lean_ctor_get(v___y_4812_, 3);
                v_maxRecDepth_4829_ = lean_ctor_get(v___y_4812_, 4);
                v_ref_4830_ = lean_ctor_get(v___y_4812_, 5);
                v___x_4831_ = lean_box(0);
                v___x_4838_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0;
                v___x_4854_ = lean_unsigned_to_nat(1);
                v___x_4855_ = lean_nat_add(v_macroScope_4820_, v___x_4854_);
                if v_isShared_4825_ == 0 {
                    lean_ctor_set(v___x_4824_, 0, v___x_4855_);
                    v___x_4857_ = v___x_4824_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4855_);
                    lean_ctor_set(v_reuseFailAlloc_4886_, 1, v_traceMsgs_4821_);
                    lean_ctor_set(v_reuseFailAlloc_4886_, 2, v_expandedMacroDecls_4822_);
                    v___x_4857_ = v_reuseFailAlloc_4886_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                v___x_4835_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4835_, 0, v_a_4833_);
                v___x_4836_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4836_, 0, v___x_4835_);
                lean_ctor_set(v___x_4836_, 1, v___x_4831_);
                v___x_4837_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4837_, 0, v___x_4836_);
                lean_ctor_set(v___x_4837_, 1, v_a_4834_);
                return v___x_4837_;
            }
            3 => {
                if lean_obj_tag(v_a_4840_) == 1 {
                    v_as_x27_4810_ = v_tail_4816_;
                    v_b_4811_ = v___x_4838_;
                    v___y_4813_ = v_a_4841_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_stx_4809_);
                    v_declName_4843_ = lean_ctor_get(v_toOLeanEntry_4817_, 1);
                    v___x_4844_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4844_, 0, v_a_4840_);
                    lean_inc(v_declName_4843_);
                    v___x_4845_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4845_, 0, v_declName_4843_);
                    lean_ctor_set(v___x_4845_, 1, v___x_4844_);
                    v___x_4846_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4846_, 0, v___x_4845_);
                    v_a_4833_ = v___x_4846_;
                    v_a_4834_ = v_a_4841_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_a_4849_ = lean_ctor_get(v___y_4848_, 0);
                if lean_obj_tag(v_a_4849_) == 0 {
                    lean_inc_ref(v_a_4849_);
                    lean_dec(v_stx_4809_);
                    v_a_4850_ = lean_ctor_get(v___y_4848_, 1);
                    lean_inc(v_a_4850_);
                    lean_dec_ref(v___y_4848_);
                    v_a_4851_ = lean_ctor_get(v_a_4849_, 0);
                    lean_inc(v_a_4851_);
                    lean_dec_ref_known(v_a_4849_, 1);
                    v_a_4833_ = v_a_4851_;
                    v_a_4834_ = v_a_4850_;
                    state = 2;
                    continue;
                } else {
                    v_a_4852_ = lean_ctor_get(v___y_4848_, 1);
                    lean_inc(v_a_4852_);
                    lean_dec_ref(v___y_4848_);
                    v_as_x27_4810_ = v_tail_4816_;
                    v_b_4811_ = v___x_4838_;
                    v___y_4813_ = v_a_4852_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                lean_inc(v_ref_4830_);
                lean_inc(v_maxRecDepth_4829_);
                lean_inc(v_currRecDepth_4828_);
                lean_inc(v_quotContext_4827_);
                lean_inc(v_methods_4826_);
                v___x_4858_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_4858_, 0, v_methods_4826_);
                lean_ctor_set(v___x_4858_, 1, v_quotContext_4827_);
                lean_ctor_set(v___x_4858_, 2, v_macroScope_4820_);
                lean_ctor_set(v___x_4858_, 3, v_currRecDepth_4828_);
                lean_ctor_set(v___x_4858_, 4, v_maxRecDepth_4829_);
                lean_ctor_set(v___x_4858_, 5, v_ref_4830_);
                lean_inc(v_value_4819_);
                lean_inc(v_stx_4809_);
                v___x_4859_ = lean_apply_3(v_value_4819_, v_stx_4809_, v___x_4858_, v___x_4857_);
                if lean_obj_tag(v___x_4859_) == 0 {
                    if v_isBuiltin_4818_ == 0 {
                        v_a_4860_ = lean_ctor_get(v___x_4859_, 1);
                        v_a_4861_ = lean_ctor_get(v___x_4859_, 0);
                        v_isSharedCheck_4880_ = (!lean_is_exclusive(v___x_4859_)) as u8;
                        if v_isSharedCheck_4880_ == 0 {
                            v___x_4863_ = v___x_4859_;
                            v_isShared_4864_ = v_isSharedCheck_4880_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4860_);
                            lean_inc(v_a_4861_);
                            lean_dec(v___x_4859_);
                            v___x_4863_ = lean_box(0);
                            v_isShared_4864_ = v_isSharedCheck_4880_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4881_ = lean_ctor_get(v___x_4859_, 0);
                        lean_inc(v_a_4881_);
                        v_a_4882_ = lean_ctor_get(v___x_4859_, 1);
                        lean_inc(v_a_4882_);
                        lean_dec_ref_known(v___x_4859_, 2);
                        lean_inc_ref(v_toOLeanEntry_4817_);
                        v___x_4883_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___lam__0(v_toOLeanEntry_4817_, v_a_4881_, v___x_4831_, v___y_4812_, v_a_4882_);
                        v___y_4848_ = v___x_4883_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4884_ = lean_ctor_get(v___x_4859_, 0);
                    lean_inc(v_a_4884_);
                    v_a_4885_ = lean_ctor_get(v___x_4859_, 1);
                    lean_inc(v_a_4885_);
                    lean_dec_ref_known(v___x_4859_, 2);
                    v_a_4840_ = v_a_4884_;
                    v_a_4841_ = v_a_4885_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                v_macroScope_4865_ = lean_ctor_get(v_a_4860_, 0);
                v_traceMsgs_4866_ = lean_ctor_get(v_a_4860_, 1);
                v_expandedMacroDecls_4867_ = lean_ctor_get(v_a_4860_, 2);
                v_isSharedCheck_4879_ = (!lean_is_exclusive(v_a_4860_)) as u8;
                if v_isSharedCheck_4879_ == 0 {
                    v___x_4869_ = v_a_4860_;
                    v_isShared_4870_ = v_isSharedCheck_4879_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_expandedMacroDecls_4867_);
                    lean_inc(v_traceMsgs_4866_);
                    lean_inc(v_macroScope_4865_);
                    lean_dec(v_a_4860_);
                    v___x_4869_ = lean_box(0);
                    v_isShared_4870_ = v_isSharedCheck_4879_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_declName_4871_ = lean_ctor_get(v_toOLeanEntry_4817_, 1);
                lean_inc(v_declName_4871_);
                if v_isShared_4864_ == 0 {
                    lean_ctor_set_tag(v___x_4863_, 1);
                    lean_ctor_set(v___x_4863_, 1, v_expandedMacroDecls_4867_);
                    lean_ctor_set(v___x_4863_, 0, v_declName_4871_);
                    v___x_4873_ = v___x_4863_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_declName_4871_);
                    lean_ctor_set(v_reuseFailAlloc_4878_, 1, v_expandedMacroDecls_4867_);
                    v___x_4873_ = v_reuseFailAlloc_4878_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4870_ == 0 {
                    lean_ctor_set(v___x_4869_, 2, v___x_4873_);
                    v___x_4875_ = v___x_4869_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_macroScope_4865_);
                    lean_ctor_set(v_reuseFailAlloc_4877_, 1, v_traceMsgs_4866_);
                    lean_ctor_set(v_reuseFailAlloc_4877_, 2, v___x_4873_);
                    v___x_4875_ = v_reuseFailAlloc_4877_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                lean_inc_ref(v_toOLeanEntry_4817_);
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
    mut v_stx_4888_: *mut LeanObject,
    mut v_as_x27_4889_: *mut LeanObject,
    mut v_b_4890_: *mut LeanObject,
    mut v___y_4891_: *mut LeanObject,
    mut v___y_4892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4893_: *mut LeanObject = core::ptr::null_mut();
    v_res_4893_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(
        v_stx_4888_,
        v_as_x27_4889_,
        v_b_4890_,
        v___y_4891_,
        v___y_4892_,
    );
    lean_dec_ref(v___y_4891_);
    lean_dec(v_as_x27_4889_);
    return v_res_4893_;
}
pub unsafe fn l_Lean_Elab_expandMacroImpl_x3f(
    mut v_env_4894_: *mut LeanObject,
    mut v_stx_4895_: *mut LeanObject,
    mut v_a_4896_: *mut LeanObject,
    mut v_a_4897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4909_: u8 = 0;
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4913_: u8 = 0;
    let mut v_unused_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v_val_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_unused_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4898_ = l_Lean_Elab_macroAttribute;
                lean_inc(v_stx_4895_);
                v___x_4899_ = l_Lean_Syntax_getKind(v_stx_4895_);
                v___x_4900_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(
                    v___x_4898_,
                    v_env_4894_,
                    v___x_4899_,
                );
                lean_dec(v___x_4899_);
                v___x_4901_ = lean_box(0);
                v___x_4902_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg___closed__0;
                v___x_4903_ =
                    l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0___redArg(
                        v_stx_4895_,
                        v___x_4900_,
                        v___x_4902_,
                        v_a_4896_,
                        v_a_4897_,
                    );
                lean_dec(v___x_4900_);
                v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
                lean_inc(v_a_4904_);
                v_fst_4905_ = lean_ctor_get(v_a_4904_, 0);
                lean_inc(v_fst_4905_);
                lean_dec(v_a_4904_);
                if lean_obj_tag(v_fst_4905_) == 0 {
                    v_a_4906_ = lean_ctor_get(v___x_4903_, 1);
                    v_isSharedCheck_4913_ = (!lean_is_exclusive(v___x_4903_)) as u8;
                    if v_isSharedCheck_4913_ == 0 {
                        v_unused_4914_ = lean_ctor_get(v___x_4903_, 0);
                        lean_dec(v_unused_4914_);
                        v___x_4908_ = v___x_4903_;
                        v_isShared_4909_ = v_isSharedCheck_4913_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4906_);
                        lean_dec(v___x_4903_);
                        v___x_4908_ = lean_box(0);
                        v_isShared_4909_ = v_isSharedCheck_4913_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4915_ = lean_ctor_get(v___x_4903_, 1);
                    v_isSharedCheck_4923_ = (!lean_is_exclusive(v___x_4903_)) as u8;
                    if v_isSharedCheck_4923_ == 0 {
                        v_unused_4924_ = lean_ctor_get(v___x_4903_, 0);
                        lean_dec(v_unused_4924_);
                        v___x_4917_ = v___x_4903_;
                        v_isShared_4918_ = v_isSharedCheck_4923_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4915_);
                        lean_dec(v___x_4903_);
                        v___x_4917_ = lean_box(0);
                        v_isShared_4918_ = v_isSharedCheck_4923_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4909_ == 0 {
                    lean_ctor_set(v___x_4908_, 0, v___x_4901_);
                    v___x_4911_ = v___x_4908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4901_);
                    lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_a_4906_);
                    v___x_4911_ = v_reuseFailAlloc_4912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4911_;
            }
            3 => {
                v_val_4919_ = lean_ctor_get(v_fst_4905_, 0);
                lean_inc(v_val_4919_);
                lean_dec_ref_known(v_fst_4905_, 1);
                if v_isShared_4918_ == 0 {
                    lean_ctor_set(v___x_4917_, 0, v_val_4919_);
                    v___x_4921_ = v___x_4917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_val_4919_);
                    lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_a_4915_);
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
    mut v_env_4925_: *mut LeanObject,
    mut v_stx_4926_: *mut LeanObject,
    mut v_a_4927_: *mut LeanObject,
    mut v_a_4928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4929_: *mut LeanObject = core::ptr::null_mut();
    v_res_4929_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_4925_, v_stx_4926_, v_a_4927_, v_a_4928_);
    lean_dec_ref(v_a_4927_);
    return v_res_4929_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(
    mut v_stx_4930_: *mut LeanObject,
    mut v_as_4931_: *mut LeanObject,
    mut v_as_x27_4932_: *mut LeanObject,
    mut v_b_4933_: *mut LeanObject,
    mut v_a_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
    mut v___y_4936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_stx_4938_: *mut LeanObject,
    mut v_as_4939_: *mut LeanObject,
    mut v_as_x27_4940_: *mut LeanObject,
    mut v_b_4941_: *mut LeanObject,
    mut v_a_4942_: *mut LeanObject,
    mut v___y_4943_: *mut LeanObject,
    mut v___y_4944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4945_: *mut LeanObject = core::ptr::null_mut();
    v_res_4945_ = l_List_forIn_x27_loop___at___00Lean_Elab_expandMacroImpl_x3f_spec__0(
        v_stx_4938_,
        v_as_4939_,
        v_as_x27_4940_,
        v_b_4941_,
        v_a_4942_,
        v___y_4943_,
        v___y_4944_,
    );
    lean_dec_ref(v___y_4943_);
    lean_dec(v_as_x27_4940_);
    lean_dec(v_as_4939_);
    return v_res_4945_;
}
pub unsafe fn l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0(
    mut v_setNextMacroScope_4946_: *mut LeanObject,
    mut v_inst_4947_: *mut LeanObject,
    mut v_s_4948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    v___x_4949_ = lean_apply_1(v_setNextMacroScope_4946_, v_s_4948_);
    v___x_4950_ = lean_apply_2(v_inst_4947_, lean_box(0), v___x_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg(
    mut v_inst_4951_: *mut LeanObject,
    mut v_inst_4952_: *mut LeanObject,
    mut v_inst_4953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getNextMacroScope_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_setNextMacroScope_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4958_: u8 = 0;
    let mut v___f_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_unused_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getNextMacroScope_4954_ = lean_ctor_get(v_inst_4953_, 1);
                v_setNextMacroScope_4955_ = lean_ctor_get(v_inst_4953_, 2);
                v_isSharedCheck_4964_ = (!lean_is_exclusive(v_inst_4953_)) as u8;
                if v_isSharedCheck_4964_ == 0 {
                    v_unused_4965_ = lean_ctor_get(v_inst_4953_, 0);
                    lean_dec(v_unused_4965_);
                    v___x_4957_ = v_inst_4953_;
                    v_isShared_4958_ = v_isSharedCheck_4964_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_setNextMacroScope_4955_);
                    lean_inc(v_getNextMacroScope_4954_);
                    lean_dec(v_inst_4953_);
                    v___x_4957_ = lean_box(0);
                    v_isShared_4958_ = v_isSharedCheck_4964_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_inst_4951_);
                v___f_4959_ = lean_alloc_closure(
                    l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_4959_, 0, v_setNextMacroScope_4955_);
                lean_closure_set(v___f_4959_, 1, v_inst_4951_);
                v___x_4960_ = lean_apply_2(v_inst_4951_, lean_box(0), v_getNextMacroScope_4954_);
                if v_isShared_4958_ == 0 {
                    lean_ctor_set(v___x_4957_, 2, v___f_4959_);
                    lean_ctor_set(v___x_4957_, 1, v___x_4960_);
                    lean_ctor_set(v___x_4957_, 0, v_inst_4952_);
                    v___x_4962_ = v___x_4957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_inst_4952_);
                    lean_ctor_set(v_reuseFailAlloc_4963_, 1, v___x_4960_);
                    lean_ctor_set(v_reuseFailAlloc_4963_, 2, v___f_4959_);
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
    mut v_m_4966_: *mut LeanObject,
    mut v_n_4967_: *mut LeanObject,
    mut v_inst_4968_: *mut LeanObject,
    mut v_inst_4969_: *mut LeanObject,
    mut v_inst_4970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getNextMacroScope_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_setNextMacroScope_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4975_: u8 = 0;
    let mut v___f_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4981_: u8 = 0;
    let mut v_unused_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getNextMacroScope_4971_ = lean_ctor_get(v_inst_4970_, 1);
                v_setNextMacroScope_4972_ = lean_ctor_get(v_inst_4970_, 2);
                v_isSharedCheck_4981_ = (!lean_is_exclusive(v_inst_4970_)) as u8;
                if v_isSharedCheck_4981_ == 0 {
                    v_unused_4982_ = lean_ctor_get(v_inst_4970_, 0);
                    lean_dec(v_unused_4982_);
                    v___x_4974_ = v_inst_4970_;
                    v_isShared_4975_ = v_isSharedCheck_4981_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_setNextMacroScope_4972_);
                    lean_inc(v_getNextMacroScope_4971_);
                    lean_dec(v_inst_4970_);
                    v___x_4974_ = lean_box(0);
                    v_isShared_4975_ = v_isSharedCheck_4981_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_inst_4968_);
                v___f_4976_ = lean_alloc_closure(
                    l_Lean_Elab_instMonadMacroAdapterOfMonadLiftOfMonadQuotation___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_4976_, 0, v_setNextMacroScope_4972_);
                lean_closure_set(v___f_4976_, 1, v_inst_4968_);
                v___x_4977_ = lean_apply_2(v_inst_4968_, lean_box(0), v_getNextMacroScope_4971_);
                if v_isShared_4975_ == 0 {
                    lean_ctor_set(v___x_4974_, 2, v___f_4976_);
                    lean_ctor_set(v___x_4974_, 1, v___x_4977_);
                    lean_ctor_set(v___x_4974_, 0, v_inst_4969_);
                    v___x_4979_ = v___x_4974_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_inst_4969_);
                    lean_ctor_set(v_reuseFailAlloc_4980_, 1, v___x_4977_);
                    lean_ctor_set(v_reuseFailAlloc_4980_, 2, v___f_4976_);
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
    mut v_toPure_4983_: *mut LeanObject,
    mut v_snd_4984_: *mut LeanObject,
    mut v_inst_4985_: *mut LeanObject,
    mut v_inst_4986_: *mut LeanObject,
    mut v_toMonadRef_4987_: *mut LeanObject,
    mut v_inst_4988_: *mut LeanObject,
    mut v_fst_4989_: *mut LeanObject,
    mut v_____do__lift_4990_: u8,
) -> *mut LeanObject {
    if v_____do__lift_4990_ == 0 {
        let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_4989_);
        lean_dec(v_inst_4988_);
        lean_dec_ref(v_toMonadRef_4987_);
        lean_dec_ref(v_inst_4986_);
        lean_dec_ref(v_inst_4985_);
        lean_dec_ref(v_snd_4984_);
        v___x_4991_ = lean_box(0);
        v___x_4992_ = lean_apply_2(v_toPure_4983_, lean_box(0), v___x_4991_);
        return v___x_4992_;
    } else {
        let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_4983_);
        v___x_4993_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_4993_, 0, v_snd_4984_);
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
    mut v_toPure_4996_: *mut LeanObject,
    mut v_snd_4997_: *mut LeanObject,
    mut v_inst_4998_: *mut LeanObject,
    mut v_inst_4999_: *mut LeanObject,
    mut v_toMonadRef_5000_: *mut LeanObject,
    mut v_inst_5001_: *mut LeanObject,
    mut v_fst_5002_: *mut LeanObject,
    mut v_____do__lift_5003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_1416__boxed_5004_: u8 = 0;
    let mut v_res_5005_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_1416__boxed_5004_ = (lean_unbox(v_____do__lift_5003_) as u8);
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
    mut v_toPure_5006_: *mut LeanObject,
    mut v_fst_5007_: *mut LeanObject,
    mut v_____do__lift_5008_: *mut LeanObject,
    mut v_____do__lift_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hasTrace_5010_: u8 = 0;
    v_hasTrace_5010_ = lean_ctor_get_uint8(
        v_____do__lift_5009_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    if v_hasTrace_5010_ == 0 {
        let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_5007_);
        v___x_5011_ = lean_box((v_hasTrace_5010_) as usize);
        v___x_5012_ = lean_apply_2(v_toPure_5006_, lean_box(0), v___x_5011_);
        return v___x_5012_;
    } else {
        let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5015_: u8 = 0;
        let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
        v___x_5013_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__14;
        v___x_5014_ = l_Lean_Name_append(v___x_5013_, v_fst_5007_);
        v___x_5015_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_5008_,
            v_____do__lift_5009_,
            v___x_5014_,
        );
        lean_dec(v___x_5014_);
        v___x_5016_ = lean_box((v___x_5015_) as usize);
        v___x_5017_ = lean_apply_2(v_toPure_5006_, lean_box(0), v___x_5016_);
        return v___x_5017_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__1___boxed(
    mut v_toPure_5018_: *mut LeanObject,
    mut v_fst_5019_: *mut LeanObject,
    mut v_____do__lift_5020_: *mut LeanObject,
    mut v_____do__lift_5021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5022_: *mut LeanObject = core::ptr::null_mut();
    v_res_5022_ = l_Lean_Elab_liftMacroM___redArg___lam__1(
        v_toPure_5018_,
        v_fst_5019_,
        v_____do__lift_5020_,
        v_____do__lift_5021_,
    );
    lean_dec_ref(v_____do__lift_5021_);
    lean_dec_ref(v_____do__lift_5020_);
    return v_res_5022_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__2(
    mut v_toPure_5023_: *mut LeanObject,
    mut v_fst_5024_: *mut LeanObject,
    mut v_toBind_5025_: *mut LeanObject,
    mut v_inst_5026_: *mut LeanObject,
    mut v_____do__lift_5027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    v___f_5028_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5028_, 0, v_toPure_5023_);
    lean_closure_set(v___f_5028_, 1, v_fst_5024_);
    lean_closure_set(v___f_5028_, 2, v_____do__lift_5027_);
    v___x_5029_ = lean_apply_4(
        v_toBind_5025_,
        lean_box(0),
        lean_box(0),
        v_inst_5026_,
        v___f_5028_,
    );
    return v___x_5029_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__3(
    mut v_inst_5030_: *mut LeanObject,
    mut v_toPure_5031_: *mut LeanObject,
    mut v_inst_5032_: *mut LeanObject,
    mut v_toMonadRef_5033_: *mut LeanObject,
    mut v_inst_5034_: *mut LeanObject,
    mut v_toBind_5035_: *mut LeanObject,
    mut v_inst_5036_: *mut LeanObject,
    mut v_x_5037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getInheritedTraceOptions_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    v_fst_5038_ = lean_ctor_get(v_x_5037_, 0);
    lean_inc_n(v_fst_5038_, 2);
    v_snd_5039_ = lean_ctor_get(v_x_5037_, 1);
    lean_inc(v_snd_5039_);
    lean_dec_ref(v_x_5037_);
    v_getInheritedTraceOptions_5040_ = lean_ctor_get(v_inst_5030_, 2);
    lean_inc(v_getInheritedTraceOptions_5040_);
    lean_inc(v_toPure_5031_);
    v___f_5041_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_5041_, 0, v_toPure_5031_);
    lean_closure_set(v___f_5041_, 1, v_snd_5039_);
    lean_closure_set(v___f_5041_, 2, v_inst_5032_);
    lean_closure_set(v___f_5041_, 3, v_inst_5030_);
    lean_closure_set(v___f_5041_, 4, v_toMonadRef_5033_);
    lean_closure_set(v___f_5041_, 5, v_inst_5034_);
    lean_closure_set(v___f_5041_, 6, v_fst_5038_);
    lean_inc_n(v_toBind_5035_, 2);
    v___f_5042_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5042_, 0, v_toPure_5031_);
    lean_closure_set(v___f_5042_, 1, v_fst_5038_);
    lean_closure_set(v___f_5042_, 2, v_toBind_5035_);
    lean_closure_set(v___f_5042_, 3, v_inst_5036_);
    v___x_5043_ = lean_apply_4(
        v_toBind_5035_,
        lean_box(0),
        lean_box(0),
        v_getInheritedTraceOptions_5040_,
        v___f_5042_,
    );
    v___x_5044_ = lean_apply_4(
        v_toBind_5035_,
        lean_box(0),
        lean_box(0),
        v___x_5043_,
        v___f_5041_,
    );
    return v___x_5044_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__4(
    mut v_env_5045_: *mut LeanObject,
    mut v___x_5046_: *mut LeanObject,
    mut v___x_5047_: *mut LeanObject,
    mut v_stx_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5056_: u8 = 0;
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5061_: u8 = 0;
    let mut v_unused_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5066_: u8 = 0;
    let mut v_snd_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5072_: u8 = 0;
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195__overap_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5078_: u8 = 0;
    let mut v_a_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199__overap_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5092_: u8 = 0;
    let mut v_isSharedCheck_5093_: u8 = 0;
    let mut v_a_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5098_: u8 = 0;
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5101_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5051_) == 0 {
                    v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
                    lean_inc(v_a_5052_);
                    if lean_obj_tag(v_a_5052_) == 0 {
                        lean_dec(v___x_5047_);
                        lean_dec_ref(v___x_5046_);
                        v_a_5053_ = lean_ctor_get(v___x_5051_, 1);
                        v_isSharedCheck_5061_ = (!lean_is_exclusive(v___x_5051_)) as u8;
                        if v_isSharedCheck_5061_ == 0 {
                            v_unused_5062_ = lean_ctor_get(v___x_5051_, 0);
                            lean_dec(v_unused_5062_);
                            v___x_5055_ = v___x_5051_;
                            v_isShared_5056_ = v_isSharedCheck_5061_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5053_);
                            lean_dec(v___x_5051_);
                            v___x_5055_ = lean_box(0);
                            v_isShared_5056_ = v_isSharedCheck_5061_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_5063_ = lean_ctor_get(v_a_5052_, 0);
                        v_isSharedCheck_5093_ = (!lean_is_exclusive(v_a_5052_)) as u8;
                        if v_isSharedCheck_5093_ == 0 {
                            v___x_5065_ = v_a_5052_;
                            v_isShared_5066_ = v_isSharedCheck_5093_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_5063_);
                            lean_dec(v_a_5052_);
                            v___x_5065_ = lean_box(0);
                            v_isShared_5066_ = v_isSharedCheck_5093_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5047_);
                    lean_dec_ref(v___x_5046_);
                    v_a_5094_ = lean_ctor_get(v___x_5051_, 0);
                    v_a_5095_ = lean_ctor_get(v___x_5051_, 1);
                    v_isSharedCheck_5102_ = (!lean_is_exclusive(v___x_5051_)) as u8;
                    if v_isSharedCheck_5102_ == 0 {
                        v___x_5097_ = v___x_5051_;
                        v_isShared_5098_ = v_isSharedCheck_5102_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5095_);
                        lean_inc(v_a_5094_);
                        lean_dec(v___x_5051_);
                        v___x_5097_ = lean_box(0);
                        v_isShared_5098_ = v_isSharedCheck_5102_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5057_ = lean_box(0);
                if v_isShared_5056_ == 0 {
                    lean_ctor_set(v___x_5055_, 0, v___x_5057_);
                    v___x_5059_ = v___x_5055_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5057_);
                    lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_a_5053_);
                    v___x_5059_ = v_reuseFailAlloc_5060_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5059_;
            }
            3 => {
                v_snd_5067_ = lean_ctor_get(v_val_5063_, 1);
                lean_inc(v_snd_5067_);
                lean_dec(v_val_5063_);
                if lean_obj_tag(v_snd_5067_) == 0 {
                    lean_del_object(v___x_5065_);
                    v_a_5068_ = lean_ctor_get(v___x_5051_, 1);
                    lean_inc(v_a_5068_);
                    lean_dec_ref_known(v___x_5051_, 2);
                    v_a_5069_ = lean_ctor_get(v_snd_5067_, 0);
                    v_isSharedCheck_5078_ = (!lean_is_exclusive(v_snd_5067_)) as u8;
                    if v_isSharedCheck_5078_ == 0 {
                        v___x_5071_ = v_snd_5067_;
                        v_isShared_5072_ = v_isSharedCheck_5078_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5069_);
                        lean_dec(v_snd_5067_);
                        v___x_5071_ = lean_box(0);
                        v_isShared_5072_ = v_isSharedCheck_5078_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_5079_ = lean_ctor_get(v___x_5051_, 1);
                    lean_inc(v_a_5079_);
                    lean_dec_ref_known(v___x_5051_, 2);
                    v_a_5080_ = lean_ctor_get(v_snd_5067_, 0);
                    v_isSharedCheck_5092_ = (!lean_is_exclusive(v_snd_5067_)) as u8;
                    if v_isSharedCheck_5092_ == 0 {
                        v___x_5082_ = v_snd_5067_;
                        v_isShared_5083_ = v_isSharedCheck_5092_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5080_);
                        lean_dec(v_snd_5067_);
                        v___x_5082_ = lean_box(0);
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
                    v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_a_5069_);
                    v___x_5074_ = v_reuseFailAlloc_5077_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1195__overap_5075_ =
                    l_liftExcept___redArg(v___x_5046_, v___x_5047_, v___x_5074_);
                lean_inc_ref(v___y_5049_);
                v___x_5076_ = lean_apply_2(v___x_1195__overap_5075_, v___y_5049_, v_a_5068_);
                return v___x_5076_;
            }
            6 => {
                if v_isShared_5066_ == 0 {
                    lean_ctor_set(v___x_5065_, 0, v_a_5080_);
                    v___x_5085_ = v___x_5065_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5080_);
                    v___x_5085_ = v_reuseFailAlloc_5091_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5083_ == 0 {
                    lean_ctor_set(v___x_5082_, 0, v___x_5085_);
                    v___x_5087_ = v___x_5082_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5090_, 0, v___x_5085_);
                    v___x_5087_ = v_reuseFailAlloc_5090_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1199__overap_5088_ =
                    l_liftExcept___redArg(v___x_5046_, v___x_5047_, v___x_5087_);
                lean_inc_ref(v___y_5049_);
                v___x_5089_ = lean_apply_2(v___x_1199__overap_5088_, v___y_5049_, v_a_5079_);
                return v___x_5089_;
            }
            9 => {
                if v_isShared_5098_ == 0 {
                    v___x_5100_ = v___x_5097_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5094_);
                    lean_ctor_set(v_reuseFailAlloc_5101_, 1, v_a_5095_);
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
    mut v_env_5103_: *mut LeanObject,
    mut v___x_5104_: *mut LeanObject,
    mut v___x_5105_: *mut LeanObject,
    mut v_stx_5106_: *mut LeanObject,
    mut v___y_5107_: *mut LeanObject,
    mut v___y_5108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5109_: *mut LeanObject = core::ptr::null_mut();
    v_res_5109_ = l_Lean_Elab_liftMacroM___redArg___lam__4(
        v_env_5103_,
        v___x_5104_,
        v___x_5105_,
        v_stx_5106_,
        v___y_5107_,
        v___y_5108_,
    );
    lean_dec_ref(v___y_5107_);
    return v_res_5109_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__5(
    mut v_env_5110_: *mut LeanObject,
    mut v_declName_5111_: *mut LeanObject,
    mut v___y_5112_: *mut LeanObject,
    mut v___y_5113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5114_: u8 = 0;
    let mut v_env_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: u8 = 0;
    let mut v___x_5118_: u8 = 0;
    v___x_5114_ = 0;
    v_env_5115_ = l_Lean_Environment_setExporting(v_env_5110_, v___x_5114_);
    lean_inc(v_declName_5111_);
    v___x_5116_ = l_Lean_mkPrivateName(v_env_5115_, v_declName_5111_);
    v___x_5117_ = 1;
    lean_inc_ref(v_env_5115_);
    v___x_5118_ = l_Lean_Environment_contains(v_env_5115_, v___x_5116_, v___x_5117_);
    if v___x_5118_ == 0 {
        let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5120_: u8 = 0;
        let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
        v___x_5119_ = l_Lean_privateToUserName(v_declName_5111_);
        v___x_5120_ = l_Lean_Environment_contains(v_env_5115_, v___x_5119_, v___x_5117_);
        v___x_5121_ = lean_box((v___x_5120_) as usize);
        v___x_5122_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5122_, 0, v___x_5121_);
        lean_ctor_set(v___x_5122_, 1, v___y_5113_);
        return v___x_5122_;
    } else {
        let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_5115_);
        lean_dec(v_declName_5111_);
        v___x_5123_ = lean_box((v___x_5118_) as usize);
        v___x_5124_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5124_, 0, v___x_5123_);
        lean_ctor_set(v___x_5124_, 1, v___y_5113_);
        return v___x_5124_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__5___boxed(
    mut v_env_5125_: *mut LeanObject,
    mut v_declName_5126_: *mut LeanObject,
    mut v___y_5127_: *mut LeanObject,
    mut v___y_5128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5129_: *mut LeanObject = core::ptr::null_mut();
    v_res_5129_ = l_Lean_Elab_liftMacroM___redArg___lam__5(
        v_env_5125_,
        v_declName_5126_,
        v___y_5127_,
        v___y_5128_,
    );
    lean_dec_ref(v___y_5127_);
    return v_res_5129_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__6(
    mut v_env_5130_: *mut LeanObject,
    mut v_currNamespace_5131_: *mut LeanObject,
    mut v_openDecls_5132_: *mut LeanObject,
    mut v_n_5133_: *mut LeanObject,
    mut v___y_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    v___x_5136_ = l_Lean_ResolveName_resolveNamespace(
        v_env_5130_,
        v_currNamespace_5131_,
        v_openDecls_5132_,
        v_n_5133_,
    );
    v___x_5137_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5137_, 0, v___x_5136_);
    lean_ctor_set(v___x_5137_, 1, v___y_5135_);
    return v___x_5137_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__6___boxed(
    mut v_env_5138_: *mut LeanObject,
    mut v_currNamespace_5139_: *mut LeanObject,
    mut v_openDecls_5140_: *mut LeanObject,
    mut v_n_5141_: *mut LeanObject,
    mut v___y_5142_: *mut LeanObject,
    mut v___y_5143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5144_: *mut LeanObject = core::ptr::null_mut();
    v_res_5144_ = l_Lean_Elab_liftMacroM___redArg___lam__6(
        v_env_5138_,
        v_currNamespace_5139_,
        v_openDecls_5140_,
        v_n_5141_,
        v___y_5142_,
        v___y_5143_,
    );
    lean_dec_ref(v___y_5142_);
    return v_res_5144_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__7(
    mut v_env_5145_: *mut LeanObject,
    mut v_opts_5146_: *mut LeanObject,
    mut v_currNamespace_5147_: *mut LeanObject,
    mut v_openDecls_5148_: *mut LeanObject,
    mut v_n_5149_: *mut LeanObject,
    mut v___y_5150_: *mut LeanObject,
    mut v___y_5151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    v___x_5152_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_5145_,
        v_opts_5146_,
        v_currNamespace_5147_,
        v_openDecls_5148_,
        v_n_5149_,
    );
    v___x_5153_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5153_, 0, v___x_5152_);
    lean_ctor_set(v___x_5153_, 1, v___y_5151_);
    return v___x_5153_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__7___boxed(
    mut v_env_5154_: *mut LeanObject,
    mut v_opts_5155_: *mut LeanObject,
    mut v_currNamespace_5156_: *mut LeanObject,
    mut v_openDecls_5157_: *mut LeanObject,
    mut v_n_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
    mut v___y_5160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5161_: *mut LeanObject = core::ptr::null_mut();
    v_res_5161_ = l_Lean_Elab_liftMacroM___redArg___lam__7(
        v_env_5154_,
        v_opts_5155_,
        v_currNamespace_5156_,
        v_openDecls_5157_,
        v_n_5158_,
        v___y_5159_,
        v___y_5160_,
    );
    lean_dec_ref(v___y_5159_);
    lean_dec_ref(v_opts_5155_);
    return v_res_5161_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__8(
    mut v_toPure_5162_: *mut LeanObject,
    mut v_a_5163_: *mut LeanObject,
    mut v_____r_5164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    v___x_5165_ = lean_apply_2(v_toPure_5162_, lean_box(0), v_a_5163_);
    return v___x_5165_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__9(
    mut v_traceMsgs_5166_: *mut LeanObject,
    mut v_inst_5167_: *mut LeanObject,
    mut v___f_5168_: *mut LeanObject,
    mut v_toBind_5169_: *mut LeanObject,
    mut v___f_5170_: *mut LeanObject,
    mut v_____r_5171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    v___x_5172_ = l_List_reverse___redArg(v_traceMsgs_5166_);
    v___x_5173_ = l_List_forM___redArg(v_inst_5167_, v___x_5172_, v___f_5168_);
    v___x_5174_ = lean_apply_4(
        v_toBind_5169_,
        lean_box(0),
        lean_box(0),
        v___x_5173_,
        v___f_5170_,
    );
    return v___x_5174_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__10(
    mut v_setNextMacroScope_5175_: *mut LeanObject,
    mut v_macroScope_5176_: *mut LeanObject,
    mut v_toBind_5177_: *mut LeanObject,
    mut v___f_5178_: *mut LeanObject,
    mut v_____s_5179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    v___x_5180_ = lean_apply_1(v_setNextMacroScope_5175_, v_macroScope_5176_);
    v___x_5181_ = lean_apply_4(
        v_toBind_5177_,
        lean_box(0),
        lean_box(0),
        v___x_5180_,
        v___f_5178_,
    );
    return v___x_5181_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__11(
    mut v___x_5182_: *mut LeanObject,
    mut v_toPure_5183_: *mut LeanObject,
    mut v_____r_5184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    v___x_5185_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5185_, 0, v___x_5182_);
    v___x_5186_ = lean_apply_2(v_toPure_5183_, lean_box(0), v___x_5185_);
    return v___x_5186_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__12(
    mut v_inst_5187_: *mut LeanObject,
    mut v_inst_5188_: *mut LeanObject,
    mut v_inst_5189_: *mut LeanObject,
    mut v_inst_5190_: *mut LeanObject,
    mut v_toMonadRef_5191_: *mut LeanObject,
    mut v_inst_5192_: *mut LeanObject,
    mut v_toBind_5193_: *mut LeanObject,
    mut v___f_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
    mut v_x_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5198_: u8 = 0;
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
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
    v___x_5200_ = lean_apply_4(
        v_toBind_5193_,
        lean_box(0),
        lean_box(0),
        v___x_5199_,
        v___f_5194_,
    );
    return v___x_5200_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__13(
    mut v_methods_5202_: *mut LeanObject,
    mut v_____do__lift_5203_: *mut LeanObject,
    mut v_____do__lift_5204_: *mut LeanObject,
    mut v_____do__lift_5205_: *mut LeanObject,
    mut v_____do__lift_5206_: *mut LeanObject,
    mut v_____do__lift_5207_: *mut LeanObject,
    mut v_x_5208_: *mut LeanObject,
    mut v_toPure_5209_: *mut LeanObject,
    mut v_inst_5210_: *mut LeanObject,
    mut v___f_5211_: *mut LeanObject,
    mut v_toBind_5212_: *mut LeanObject,
    mut v_setNextMacroScope_5213_: *mut LeanObject,
    mut v_inst_5214_: *mut LeanObject,
    mut v_inst_5215_: *mut LeanObject,
    mut v_inst_5216_: *mut LeanObject,
    mut v_toMonadRef_5217_: *mut LeanObject,
    mut v_inst_5218_: *mut LeanObject,
    mut v_inst_5219_: *mut LeanObject,
    mut v_toMonadExceptOf_5220_: *mut LeanObject,
    mut v_____do__lift_5221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    v___x_5222_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_5222_, 0, v_methods_5202_);
    lean_ctor_set(v___x_5222_, 1, v_____do__lift_5203_);
    lean_ctor_set(v___x_5222_, 2, v_____do__lift_5204_);
    lean_ctor_set(v___x_5222_, 3, v_____do__lift_5205_);
    lean_ctor_set(v___x_5222_, 4, v_____do__lift_5206_);
    lean_ctor_set(v___x_5222_, 5, v_____do__lift_5207_);
    v___x_5223_ = lean_box(0);
    v___x_5224_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5224_, 0, v_____do__lift_5221_);
    lean_ctor_set(v___x_5224_, 1, v___x_5223_);
    lean_ctor_set(v___x_5224_, 2, v___x_5223_);
    v___x_5225_ = lean_apply_2(v_x_5208_, v___x_5222_, v___x_5224_);
    if lean_obj_tag(v___x_5225_) == 0 {
        let mut v_a_5226_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_5227_: *mut LeanObject = core::ptr::null_mut();
        let mut v_macroScope_5228_: *mut LeanObject = core::ptr::null_mut();
        let mut v_traceMsgs_5229_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expandedMacroDecls_5230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5231_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toMonadExceptOf_5220_);
        lean_dec_ref(v_inst_5219_);
        v_a_5226_ = lean_ctor_get(v___x_5225_, 1);
        lean_inc(v_a_5226_);
        v_a_5227_ = lean_ctor_get(v___x_5225_, 0);
        lean_inc(v_a_5227_);
        lean_dec_ref_known(v___x_5225_, 2);
        v_macroScope_5228_ = lean_ctor_get(v_a_5226_, 0);
        lean_inc(v_macroScope_5228_);
        v_traceMsgs_5229_ = lean_ctor_get(v_a_5226_, 1);
        lean_inc(v_traceMsgs_5229_);
        v_expandedMacroDecls_5230_ = lean_ctor_get(v_a_5226_, 2);
        lean_inc(v_expandedMacroDecls_5230_);
        lean_dec(v_a_5226_);
        lean_inc(v_toPure_5209_);
        v___f_5231_ = lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__8 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_5231_, 0, v_toPure_5209_);
        lean_closure_set(v___f_5231_, 1, v_a_5227_);
        lean_inc_n(v_toBind_5212_, 3);
        lean_inc_ref_n(v_inst_5210_, 2);
        v___f_5232_ = lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__9 as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_5232_, 0, v_traceMsgs_5229_);
        lean_closure_set(v___f_5232_, 1, v_inst_5210_);
        lean_closure_set(v___f_5232_, 2, v___f_5211_);
        lean_closure_set(v___f_5232_, 3, v_toBind_5212_);
        lean_closure_set(v___f_5232_, 4, v___f_5231_);
        v___f_5233_ = lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__10 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_5233_, 0, v_setNextMacroScope_5213_);
        lean_closure_set(v___f_5233_, 1, v_macroScope_5228_);
        lean_closure_set(v___f_5233_, 2, v_toBind_5212_);
        lean_closure_set(v___f_5233_, 3, v___f_5232_);
        v___x_5234_ = lean_box(0);
        v___f_5235_ = lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__11 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_5235_, 0, v___x_5234_);
        lean_closure_set(v___f_5235_, 1, v_toPure_5209_);
        v___f_5236_ = lean_alloc_closure(
            l_Lean_Elab_liftMacroM___redArg___lam__12 as *mut core::ffi::c_void,
            11,
            8,
        );
        lean_closure_set(v___f_5236_, 0, v_inst_5210_);
        lean_closure_set(v___f_5236_, 1, v_inst_5214_);
        lean_closure_set(v___f_5236_, 2, v_inst_5215_);
        lean_closure_set(v___f_5236_, 3, v_inst_5216_);
        lean_closure_set(v___f_5236_, 4, v_toMonadRef_5217_);
        lean_closure_set(v___f_5236_, 5, v_inst_5218_);
        lean_closure_set(v___f_5236_, 6, v_toBind_5212_);
        lean_closure_set(v___f_5236_, 7, v___f_5235_);
        v___x_5237_ = l_List_forIn_x27_loop___redArg(
            v_inst_5210_,
            v___f_5236_,
            v_expandedMacroDecls_5230_,
            v___x_5234_,
        );
        lean_dec(v_expandedMacroDecls_5230_);
        v___x_5238_ = lean_apply_4(
            v_toBind_5212_,
            lean_box(0),
            lean_box(0),
            v___x_5237_,
            v___f_5233_,
        );
        return v___x_5238_;
    } else {
        let mut v_a_5239_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_5218_);
        lean_dec_ref(v_toMonadRef_5217_);
        lean_dec(v_inst_5216_);
        lean_dec_ref(v_inst_5215_);
        lean_dec_ref(v_inst_5214_);
        lean_dec(v_setNextMacroScope_5213_);
        lean_dec(v_toBind_5212_);
        lean_dec(v___f_5211_);
        lean_dec(v_toPure_5209_);
        v_a_5239_ = lean_ctor_get(v___x_5225_, 0);
        lean_inc(v_a_5239_);
        lean_dec_ref_known(v___x_5225_, 2);
        if lean_obj_tag(v_a_5239_) == 0 {
            let mut v_a_5240_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_5241_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5243_: u8 = 0;
            lean_dec_ref(v_toMonadExceptOf_5220_);
            v_a_5240_ = lean_ctor_get(v_a_5239_, 0);
            lean_inc(v_a_5240_);
            v_a_5241_ = lean_ctor_get(v_a_5239_, 1);
            lean_inc_ref(v_a_5241_);
            lean_dec_ref_known(v_a_5239_, 2);
            v___x_5242_ = l_Lean_Elab_liftMacroM___redArg___lam__13___closed__0;
            v___x_5243_ = lean_string_dec_eq(v_a_5241_, v___x_5242_);
            if v___x_5243_ == 0 {
                let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
                v___x_5244_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5244_, 0, v_a_5241_);
                v___x_5245_ = l_Lean_MessageData_ofFormat(v___x_5244_);
                v___x_5246_ = l_Lean_throwErrorAt___redArg(
                    v_inst_5210_,
                    v_inst_5219_,
                    v_a_5240_,
                    v___x_5245_,
                );
                return v___x_5246_;
            } else {
                let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_a_5241_);
                lean_dec_ref(v_inst_5210_);
                v___x_5247_ = l_Lean_throwMaxRecDepthAt___redArg(v_inst_5219_, v_a_5240_);
                return v___x_5247_;
            }
        } else {
            let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_5219_);
            lean_dec_ref(v_inst_5210_);
            v___x_5248_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_toMonadExceptOf_5220_);
            return v___x_5248_;
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__13___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_methods_5249_: *mut LeanObject = *_args.add(0);
    let mut v_____do__lift_5250_: *mut LeanObject = *_args.add(1);
    let mut v_____do__lift_5251_: *mut LeanObject = *_args.add(2);
    let mut v_____do__lift_5252_: *mut LeanObject = *_args.add(3);
    let mut v_____do__lift_5253_: *mut LeanObject = *_args.add(4);
    let mut v_____do__lift_5254_: *mut LeanObject = *_args.add(5);
    let mut v_x_5255_: *mut LeanObject = *_args.add(6);
    let mut v_toPure_5256_: *mut LeanObject = *_args.add(7);
    let mut v_inst_5257_: *mut LeanObject = *_args.add(8);
    let mut v___f_5258_: *mut LeanObject = *_args.add(9);
    let mut v_toBind_5259_: *mut LeanObject = *_args.add(10);
    let mut v_setNextMacroScope_5260_: *mut LeanObject = *_args.add(11);
    let mut v_inst_5261_: *mut LeanObject = *_args.add(12);
    let mut v_inst_5262_: *mut LeanObject = *_args.add(13);
    let mut v_inst_5263_: *mut LeanObject = *_args.add(14);
    let mut v_toMonadRef_5264_: *mut LeanObject = *_args.add(15);
    let mut v_inst_5265_: *mut LeanObject = *_args.add(16);
    let mut v_inst_5266_: *mut LeanObject = *_args.add(17);
    let mut v_toMonadExceptOf_5267_: *mut LeanObject = *_args.add(18);
    let mut v_____do__lift_5268_: *mut LeanObject = *_args.add(19);
    let mut v_res_5269_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_methods_5270_: *mut LeanObject,
    mut v_____do__lift_5271_: *mut LeanObject,
    mut v_____do__lift_5272_: *mut LeanObject,
    mut v_____do__lift_5273_: *mut LeanObject,
    mut v_____do__lift_5274_: *mut LeanObject,
    mut v_x_5275_: *mut LeanObject,
    mut v_toPure_5276_: *mut LeanObject,
    mut v_inst_5277_: *mut LeanObject,
    mut v___f_5278_: *mut LeanObject,
    mut v_toBind_5279_: *mut LeanObject,
    mut v_setNextMacroScope_5280_: *mut LeanObject,
    mut v_inst_5281_: *mut LeanObject,
    mut v_inst_5282_: *mut LeanObject,
    mut v_inst_5283_: *mut LeanObject,
    mut v_toMonadRef_5284_: *mut LeanObject,
    mut v_inst_5285_: *mut LeanObject,
    mut v_inst_5286_: *mut LeanObject,
    mut v_toMonadExceptOf_5287_: *mut LeanObject,
    mut v_getNextMacroScope_5288_: *mut LeanObject,
    mut v_____do__lift_5289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_5279_);
    v___f_5290_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__13___boxed as *mut core::ffi::c_void,
        20,
        19,
    );
    lean_closure_set(v___f_5290_, 0, v_methods_5270_);
    lean_closure_set(v___f_5290_, 1, v_____do__lift_5271_);
    lean_closure_set(v___f_5290_, 2, v_____do__lift_5272_);
    lean_closure_set(v___f_5290_, 3, v_____do__lift_5273_);
    lean_closure_set(v___f_5290_, 4, v_____do__lift_5289_);
    lean_closure_set(v___f_5290_, 5, v_____do__lift_5274_);
    lean_closure_set(v___f_5290_, 6, v_x_5275_);
    lean_closure_set(v___f_5290_, 7, v_toPure_5276_);
    lean_closure_set(v___f_5290_, 8, v_inst_5277_);
    lean_closure_set(v___f_5290_, 9, v___f_5278_);
    lean_closure_set(v___f_5290_, 10, v_toBind_5279_);
    lean_closure_set(v___f_5290_, 11, v_setNextMacroScope_5280_);
    lean_closure_set(v___f_5290_, 12, v_inst_5281_);
    lean_closure_set(v___f_5290_, 13, v_inst_5282_);
    lean_closure_set(v___f_5290_, 14, v_inst_5283_);
    lean_closure_set(v___f_5290_, 15, v_toMonadRef_5284_);
    lean_closure_set(v___f_5290_, 16, v_inst_5285_);
    lean_closure_set(v___f_5290_, 17, v_inst_5286_);
    lean_closure_set(v___f_5290_, 18, v_toMonadExceptOf_5287_);
    v___x_5291_ = lean_apply_4(
        v_toBind_5279_,
        lean_box(0),
        lean_box(0),
        v_getNextMacroScope_5288_,
        v___f_5290_,
    );
    return v___x_5291_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__14___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_methods_5292_: *mut LeanObject = *_args.add(0);
    let mut v_____do__lift_5293_: *mut LeanObject = *_args.add(1);
    let mut v_____do__lift_5294_: *mut LeanObject = *_args.add(2);
    let mut v_____do__lift_5295_: *mut LeanObject = *_args.add(3);
    let mut v_____do__lift_5296_: *mut LeanObject = *_args.add(4);
    let mut v_x_5297_: *mut LeanObject = *_args.add(5);
    let mut v_toPure_5298_: *mut LeanObject = *_args.add(6);
    let mut v_inst_5299_: *mut LeanObject = *_args.add(7);
    let mut v___f_5300_: *mut LeanObject = *_args.add(8);
    let mut v_toBind_5301_: *mut LeanObject = *_args.add(9);
    let mut v_setNextMacroScope_5302_: *mut LeanObject = *_args.add(10);
    let mut v_inst_5303_: *mut LeanObject = *_args.add(11);
    let mut v_inst_5304_: *mut LeanObject = *_args.add(12);
    let mut v_inst_5305_: *mut LeanObject = *_args.add(13);
    let mut v_toMonadRef_5306_: *mut LeanObject = *_args.add(14);
    let mut v_inst_5307_: *mut LeanObject = *_args.add(15);
    let mut v_inst_5308_: *mut LeanObject = *_args.add(16);
    let mut v_toMonadExceptOf_5309_: *mut LeanObject = *_args.add(17);
    let mut v_getNextMacroScope_5310_: *mut LeanObject = *_args.add(18);
    let mut v_____do__lift_5311_: *mut LeanObject = *_args.add(19);
    let mut v_res_5312_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_methods_5313_: *mut LeanObject,
    mut v_____do__lift_5314_: *mut LeanObject,
    mut v_____do__lift_5315_: *mut LeanObject,
    mut v_____do__lift_5316_: *mut LeanObject,
    mut v_x_5317_: *mut LeanObject,
    mut v_toPure_5318_: *mut LeanObject,
    mut v_inst_5319_: *mut LeanObject,
    mut v___f_5320_: *mut LeanObject,
    mut v_toBind_5321_: *mut LeanObject,
    mut v_setNextMacroScope_5322_: *mut LeanObject,
    mut v_inst_5323_: *mut LeanObject,
    mut v_inst_5324_: *mut LeanObject,
    mut v_inst_5325_: *mut LeanObject,
    mut v_toMonadRef_5326_: *mut LeanObject,
    mut v_inst_5327_: *mut LeanObject,
    mut v_inst_5328_: *mut LeanObject,
    mut v_toMonadExceptOf_5329_: *mut LeanObject,
    mut v_getNextMacroScope_5330_: *mut LeanObject,
    mut v_getMaxRecDepth_5331_: *mut LeanObject,
    mut v_____do__lift_5332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_5321_);
    v___f_5333_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__14___boxed as *mut core::ffi::c_void,
        20,
        19,
    );
    lean_closure_set(v___f_5333_, 0, v_methods_5313_);
    lean_closure_set(v___f_5333_, 1, v_____do__lift_5314_);
    lean_closure_set(v___f_5333_, 2, v_____do__lift_5315_);
    lean_closure_set(v___f_5333_, 3, v_____do__lift_5332_);
    lean_closure_set(v___f_5333_, 4, v_____do__lift_5316_);
    lean_closure_set(v___f_5333_, 5, v_x_5317_);
    lean_closure_set(v___f_5333_, 6, v_toPure_5318_);
    lean_closure_set(v___f_5333_, 7, v_inst_5319_);
    lean_closure_set(v___f_5333_, 8, v___f_5320_);
    lean_closure_set(v___f_5333_, 9, v_toBind_5321_);
    lean_closure_set(v___f_5333_, 10, v_setNextMacroScope_5322_);
    lean_closure_set(v___f_5333_, 11, v_inst_5323_);
    lean_closure_set(v___f_5333_, 12, v_inst_5324_);
    lean_closure_set(v___f_5333_, 13, v_inst_5325_);
    lean_closure_set(v___f_5333_, 14, v_toMonadRef_5326_);
    lean_closure_set(v___f_5333_, 15, v_inst_5327_);
    lean_closure_set(v___f_5333_, 16, v_inst_5328_);
    lean_closure_set(v___f_5333_, 17, v_toMonadExceptOf_5329_);
    lean_closure_set(v___f_5333_, 18, v_getNextMacroScope_5330_);
    v___x_5334_ = lean_apply_4(
        v_toBind_5321_,
        lean_box(0),
        lean_box(0),
        v_getMaxRecDepth_5331_,
        v___f_5333_,
    );
    return v___x_5334_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__15___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_methods_5335_: *mut LeanObject = *_args.add(0);
    let mut v_____do__lift_5336_: *mut LeanObject = *_args.add(1);
    let mut v_____do__lift_5337_: *mut LeanObject = *_args.add(2);
    let mut v_____do__lift_5338_: *mut LeanObject = *_args.add(3);
    let mut v_x_5339_: *mut LeanObject = *_args.add(4);
    let mut v_toPure_5340_: *mut LeanObject = *_args.add(5);
    let mut v_inst_5341_: *mut LeanObject = *_args.add(6);
    let mut v___f_5342_: *mut LeanObject = *_args.add(7);
    let mut v_toBind_5343_: *mut LeanObject = *_args.add(8);
    let mut v_setNextMacroScope_5344_: *mut LeanObject = *_args.add(9);
    let mut v_inst_5345_: *mut LeanObject = *_args.add(10);
    let mut v_inst_5346_: *mut LeanObject = *_args.add(11);
    let mut v_inst_5347_: *mut LeanObject = *_args.add(12);
    let mut v_toMonadRef_5348_: *mut LeanObject = *_args.add(13);
    let mut v_inst_5349_: *mut LeanObject = *_args.add(14);
    let mut v_inst_5350_: *mut LeanObject = *_args.add(15);
    let mut v_toMonadExceptOf_5351_: *mut LeanObject = *_args.add(16);
    let mut v_getNextMacroScope_5352_: *mut LeanObject = *_args.add(17);
    let mut v_getMaxRecDepth_5353_: *mut LeanObject = *_args.add(18);
    let mut v_____do__lift_5354_: *mut LeanObject = *_args.add(19);
    let mut v_res_5355_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_5356_: *mut LeanObject,
    mut v_methods_5357_: *mut LeanObject,
    mut v_____do__lift_5358_: *mut LeanObject,
    mut v_____do__lift_5359_: *mut LeanObject,
    mut v_x_5360_: *mut LeanObject,
    mut v_toPure_5361_: *mut LeanObject,
    mut v_inst_5362_: *mut LeanObject,
    mut v___f_5363_: *mut LeanObject,
    mut v_toBind_5364_: *mut LeanObject,
    mut v_setNextMacroScope_5365_: *mut LeanObject,
    mut v_inst_5366_: *mut LeanObject,
    mut v_inst_5367_: *mut LeanObject,
    mut v_inst_5368_: *mut LeanObject,
    mut v_toMonadRef_5369_: *mut LeanObject,
    mut v_inst_5370_: *mut LeanObject,
    mut v_inst_5371_: *mut LeanObject,
    mut v_toMonadExceptOf_5372_: *mut LeanObject,
    mut v_getNextMacroScope_5373_: *mut LeanObject,
    mut v_____do__lift_5374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRecDepth_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getMaxRecDepth_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    v_getRecDepth_5375_ = lean_ctor_get(v_inst_5356_, 1);
    lean_inc(v_getRecDepth_5375_);
    v_getMaxRecDepth_5376_ = lean_ctor_get(v_inst_5356_, 2);
    lean_inc(v_getMaxRecDepth_5376_);
    lean_dec_ref(v_inst_5356_);
    lean_inc(v_toBind_5364_);
    v___f_5377_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__15___boxed as *mut core::ffi::c_void,
        20,
        19,
    );
    lean_closure_set(v___f_5377_, 0, v_methods_5357_);
    lean_closure_set(v___f_5377_, 1, v_____do__lift_5374_);
    lean_closure_set(v___f_5377_, 2, v_____do__lift_5358_);
    lean_closure_set(v___f_5377_, 3, v_____do__lift_5359_);
    lean_closure_set(v___f_5377_, 4, v_x_5360_);
    lean_closure_set(v___f_5377_, 5, v_toPure_5361_);
    lean_closure_set(v___f_5377_, 6, v_inst_5362_);
    lean_closure_set(v___f_5377_, 7, v___f_5363_);
    lean_closure_set(v___f_5377_, 8, v_toBind_5364_);
    lean_closure_set(v___f_5377_, 9, v_setNextMacroScope_5365_);
    lean_closure_set(v___f_5377_, 10, v_inst_5366_);
    lean_closure_set(v___f_5377_, 11, v_inst_5367_);
    lean_closure_set(v___f_5377_, 12, v_inst_5368_);
    lean_closure_set(v___f_5377_, 13, v_toMonadRef_5369_);
    lean_closure_set(v___f_5377_, 14, v_inst_5370_);
    lean_closure_set(v___f_5377_, 15, v_inst_5371_);
    lean_closure_set(v___f_5377_, 16, v_toMonadExceptOf_5372_);
    lean_closure_set(v___f_5377_, 17, v_getNextMacroScope_5373_);
    lean_closure_set(v___f_5377_, 18, v_getMaxRecDepth_5376_);
    v___x_5378_ = lean_apply_4(
        v_toBind_5364_,
        lean_box(0),
        lean_box(0),
        v_getRecDepth_5375_,
        v___f_5377_,
    );
    return v___x_5378_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__16___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_5379_: *mut LeanObject = *_args.add(0);
    let mut v_methods_5380_: *mut LeanObject = *_args.add(1);
    let mut v_____do__lift_5381_: *mut LeanObject = *_args.add(2);
    let mut v_____do__lift_5382_: *mut LeanObject = *_args.add(3);
    let mut v_x_5383_: *mut LeanObject = *_args.add(4);
    let mut v_toPure_5384_: *mut LeanObject = *_args.add(5);
    let mut v_inst_5385_: *mut LeanObject = *_args.add(6);
    let mut v___f_5386_: *mut LeanObject = *_args.add(7);
    let mut v_toBind_5387_: *mut LeanObject = *_args.add(8);
    let mut v_setNextMacroScope_5388_: *mut LeanObject = *_args.add(9);
    let mut v_inst_5389_: *mut LeanObject = *_args.add(10);
    let mut v_inst_5390_: *mut LeanObject = *_args.add(11);
    let mut v_inst_5391_: *mut LeanObject = *_args.add(12);
    let mut v_toMonadRef_5392_: *mut LeanObject = *_args.add(13);
    let mut v_inst_5393_: *mut LeanObject = *_args.add(14);
    let mut v_inst_5394_: *mut LeanObject = *_args.add(15);
    let mut v_toMonadExceptOf_5395_: *mut LeanObject = *_args.add(16);
    let mut v_getNextMacroScope_5396_: *mut LeanObject = *_args.add(17);
    let mut v_____do__lift_5397_: *mut LeanObject = *_args.add(18);
    let mut v_res_5398_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_5399_: *mut LeanObject,
    mut v_methods_5400_: *mut LeanObject,
    mut v_____do__lift_5401_: *mut LeanObject,
    mut v_x_5402_: *mut LeanObject,
    mut v_toPure_5403_: *mut LeanObject,
    mut v_inst_5404_: *mut LeanObject,
    mut v___f_5405_: *mut LeanObject,
    mut v_toBind_5406_: *mut LeanObject,
    mut v_setNextMacroScope_5407_: *mut LeanObject,
    mut v_inst_5408_: *mut LeanObject,
    mut v_inst_5409_: *mut LeanObject,
    mut v_inst_5410_: *mut LeanObject,
    mut v_toMonadRef_5411_: *mut LeanObject,
    mut v_inst_5412_: *mut LeanObject,
    mut v_inst_5413_: *mut LeanObject,
    mut v_toMonadExceptOf_5414_: *mut LeanObject,
    mut v_getNextMacroScope_5415_: *mut LeanObject,
    mut v_getContext_5416_: *mut LeanObject,
    mut v_____do__lift_5417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_5406_);
    v___f_5418_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__16___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    lean_closure_set(v___f_5418_, 0, v_inst_5399_);
    lean_closure_set(v___f_5418_, 1, v_methods_5400_);
    lean_closure_set(v___f_5418_, 2, v_____do__lift_5417_);
    lean_closure_set(v___f_5418_, 3, v_____do__lift_5401_);
    lean_closure_set(v___f_5418_, 4, v_x_5402_);
    lean_closure_set(v___f_5418_, 5, v_toPure_5403_);
    lean_closure_set(v___f_5418_, 6, v_inst_5404_);
    lean_closure_set(v___f_5418_, 7, v___f_5405_);
    lean_closure_set(v___f_5418_, 8, v_toBind_5406_);
    lean_closure_set(v___f_5418_, 9, v_setNextMacroScope_5407_);
    lean_closure_set(v___f_5418_, 10, v_inst_5408_);
    lean_closure_set(v___f_5418_, 11, v_inst_5409_);
    lean_closure_set(v___f_5418_, 12, v_inst_5410_);
    lean_closure_set(v___f_5418_, 13, v_toMonadRef_5411_);
    lean_closure_set(v___f_5418_, 14, v_inst_5412_);
    lean_closure_set(v___f_5418_, 15, v_inst_5413_);
    lean_closure_set(v___f_5418_, 16, v_toMonadExceptOf_5414_);
    lean_closure_set(v___f_5418_, 17, v_getNextMacroScope_5415_);
    v___x_5419_ = lean_apply_4(
        v_toBind_5406_,
        lean_box(0),
        lean_box(0),
        v_getContext_5416_,
        v___f_5418_,
    );
    return v___x_5419_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__17___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_5420_: *mut LeanObject = *_args.add(0);
    let mut v_methods_5421_: *mut LeanObject = *_args.add(1);
    let mut v_____do__lift_5422_: *mut LeanObject = *_args.add(2);
    let mut v_x_5423_: *mut LeanObject = *_args.add(3);
    let mut v_toPure_5424_: *mut LeanObject = *_args.add(4);
    let mut v_inst_5425_: *mut LeanObject = *_args.add(5);
    let mut v___f_5426_: *mut LeanObject = *_args.add(6);
    let mut v_toBind_5427_: *mut LeanObject = *_args.add(7);
    let mut v_setNextMacroScope_5428_: *mut LeanObject = *_args.add(8);
    let mut v_inst_5429_: *mut LeanObject = *_args.add(9);
    let mut v_inst_5430_: *mut LeanObject = *_args.add(10);
    let mut v_inst_5431_: *mut LeanObject = *_args.add(11);
    let mut v_toMonadRef_5432_: *mut LeanObject = *_args.add(12);
    let mut v_inst_5433_: *mut LeanObject = *_args.add(13);
    let mut v_inst_5434_: *mut LeanObject = *_args.add(14);
    let mut v_toMonadExceptOf_5435_: *mut LeanObject = *_args.add(15);
    let mut v_getNextMacroScope_5436_: *mut LeanObject = *_args.add(16);
    let mut v_getContext_5437_: *mut LeanObject = *_args.add(17);
    let mut v_____do__lift_5438_: *mut LeanObject = *_args.add(18);
    let mut v_res_5439_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_toMonadQuotation_5440_: *mut LeanObject,
    mut v_inst_5441_: *mut LeanObject,
    mut v_methods_5442_: *mut LeanObject,
    mut v_x_5443_: *mut LeanObject,
    mut v_toPure_5444_: *mut LeanObject,
    mut v_inst_5445_: *mut LeanObject,
    mut v___f_5446_: *mut LeanObject,
    mut v_toBind_5447_: *mut LeanObject,
    mut v_setNextMacroScope_5448_: *mut LeanObject,
    mut v_inst_5449_: *mut LeanObject,
    mut v_inst_5450_: *mut LeanObject,
    mut v_inst_5451_: *mut LeanObject,
    mut v_toMonadRef_5452_: *mut LeanObject,
    mut v_inst_5453_: *mut LeanObject,
    mut v_inst_5454_: *mut LeanObject,
    mut v_toMonadExceptOf_5455_: *mut LeanObject,
    mut v_getNextMacroScope_5456_: *mut LeanObject,
    mut v_____do__lift_5457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getCurrMacroScope_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getContext_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    v_getCurrMacroScope_5458_ = lean_ctor_get(v_toMonadQuotation_5440_, 1);
    lean_inc(v_getCurrMacroScope_5458_);
    v_getContext_5459_ = lean_ctor_get(v_toMonadQuotation_5440_, 2);
    lean_inc(v_getContext_5459_);
    lean_dec_ref(v_toMonadQuotation_5440_);
    lean_inc(v_toBind_5447_);
    v___f_5460_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__17___boxed as *mut core::ffi::c_void,
        19,
        18,
    );
    lean_closure_set(v___f_5460_, 0, v_inst_5441_);
    lean_closure_set(v___f_5460_, 1, v_methods_5442_);
    lean_closure_set(v___f_5460_, 2, v_____do__lift_5457_);
    lean_closure_set(v___f_5460_, 3, v_x_5443_);
    lean_closure_set(v___f_5460_, 4, v_toPure_5444_);
    lean_closure_set(v___f_5460_, 5, v_inst_5445_);
    lean_closure_set(v___f_5460_, 6, v___f_5446_);
    lean_closure_set(v___f_5460_, 7, v_toBind_5447_);
    lean_closure_set(v___f_5460_, 8, v_setNextMacroScope_5448_);
    lean_closure_set(v___f_5460_, 9, v_inst_5449_);
    lean_closure_set(v___f_5460_, 10, v_inst_5450_);
    lean_closure_set(v___f_5460_, 11, v_inst_5451_);
    lean_closure_set(v___f_5460_, 12, v_toMonadRef_5452_);
    lean_closure_set(v___f_5460_, 13, v_inst_5453_);
    lean_closure_set(v___f_5460_, 14, v_inst_5454_);
    lean_closure_set(v___f_5460_, 15, v_toMonadExceptOf_5455_);
    lean_closure_set(v___f_5460_, 16, v_getNextMacroScope_5456_);
    lean_closure_set(v___f_5460_, 17, v_getContext_5459_);
    v___x_5461_ = lean_apply_4(
        v_toBind_5447_,
        lean_box(0),
        lean_box(0),
        v_getCurrMacroScope_5458_,
        v___f_5460_,
    );
    return v___x_5461_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__18___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadQuotation_5462_: *mut LeanObject = *_args.add(0);
    let mut v_inst_5463_: *mut LeanObject = *_args.add(1);
    let mut v_methods_5464_: *mut LeanObject = *_args.add(2);
    let mut v_x_5465_: *mut LeanObject = *_args.add(3);
    let mut v_toPure_5466_: *mut LeanObject = *_args.add(4);
    let mut v_inst_5467_: *mut LeanObject = *_args.add(5);
    let mut v___f_5468_: *mut LeanObject = *_args.add(6);
    let mut v_toBind_5469_: *mut LeanObject = *_args.add(7);
    let mut v_setNextMacroScope_5470_: *mut LeanObject = *_args.add(8);
    let mut v_inst_5471_: *mut LeanObject = *_args.add(9);
    let mut v_inst_5472_: *mut LeanObject = *_args.add(10);
    let mut v_inst_5473_: *mut LeanObject = *_args.add(11);
    let mut v_toMonadRef_5474_: *mut LeanObject = *_args.add(12);
    let mut v_inst_5475_: *mut LeanObject = *_args.add(13);
    let mut v_inst_5476_: *mut LeanObject = *_args.add(14);
    let mut v_toMonadExceptOf_5477_: *mut LeanObject = *_args.add(15);
    let mut v_getNextMacroScope_5478_: *mut LeanObject = *_args.add(16);
    let mut v_____do__lift_5479_: *mut LeanObject = *_args.add(17);
    let mut v_res_5480_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_toMonadRef_5481_: *mut LeanObject,
    mut v_env_5482_: *mut LeanObject,
    mut v_currNamespace_5483_: *mut LeanObject,
    mut v_opts_5484_: *mut LeanObject,
    mut v___x_5485_: *mut LeanObject,
    mut v___f_5486_: *mut LeanObject,
    mut v___f_5487_: *mut LeanObject,
    mut v_toMonadQuotation_5488_: *mut LeanObject,
    mut v_inst_5489_: *mut LeanObject,
    mut v_x_5490_: *mut LeanObject,
    mut v_toPure_5491_: *mut LeanObject,
    mut v_inst_5492_: *mut LeanObject,
    mut v___f_5493_: *mut LeanObject,
    mut v_toBind_5494_: *mut LeanObject,
    mut v_setNextMacroScope_5495_: *mut LeanObject,
    mut v_inst_5496_: *mut LeanObject,
    mut v_inst_5497_: *mut LeanObject,
    mut v_inst_5498_: *mut LeanObject,
    mut v_inst_5499_: *mut LeanObject,
    mut v_inst_5500_: *mut LeanObject,
    mut v_toMonadExceptOf_5501_: *mut LeanObject,
    mut v_getNextMacroScope_5502_: *mut LeanObject,
    mut v_openDecls_5503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getRef_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    v_getRef_5504_ = lean_ctor_get(v_toMonadRef_5481_, 0);
    lean_inc(v_getRef_5504_);
    lean_inc(v_openDecls_5503_);
    lean_inc_n(v_currNamespace_5483_, 2);
    lean_inc_ref(v_env_5482_);
    v___f_5505_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__6___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_5505_, 0, v_env_5482_);
    lean_closure_set(v___f_5505_, 1, v_currNamespace_5483_);
    lean_closure_set(v___f_5505_, 2, v_openDecls_5503_);
    v___f_5506_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__7___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_5506_, 0, v_env_5482_);
    lean_closure_set(v___f_5506_, 1, v_opts_5484_);
    lean_closure_set(v___f_5506_, 2, v_currNamespace_5483_);
    lean_closure_set(v___f_5506_, 3, v_openDecls_5503_);
    v___x_5507_ = lean_alloc_closure(l_ReaderT_pure___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_5507_, 0, lean_box(0));
    lean_closure_set(v___x_5507_, 1, lean_box(0));
    lean_closure_set(v___x_5507_, 2, v___x_5485_);
    lean_closure_set(v___x_5507_, 3, lean_box(0));
    lean_closure_set(v___x_5507_, 4, v_currNamespace_5483_);
    v_methods_5508_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v_methods_5508_, 0, v___f_5486_);
    lean_ctor_set(v_methods_5508_, 1, v___x_5507_);
    lean_ctor_set(v_methods_5508_, 2, v___f_5487_);
    lean_ctor_set(v_methods_5508_, 3, v___f_5505_);
    lean_ctor_set(v_methods_5508_, 4, v___f_5506_);
    lean_inc(v_toBind_5494_);
    v___f_5509_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__18___boxed as *mut core::ffi::c_void,
        18,
        17,
    );
    lean_closure_set(v___f_5509_, 0, v_toMonadQuotation_5488_);
    lean_closure_set(v___f_5509_, 1, v_inst_5489_);
    lean_closure_set(v___f_5509_, 2, v_methods_5508_);
    lean_closure_set(v___f_5509_, 3, v_x_5490_);
    lean_closure_set(v___f_5509_, 4, v_toPure_5491_);
    lean_closure_set(v___f_5509_, 5, v_inst_5492_);
    lean_closure_set(v___f_5509_, 6, v___f_5493_);
    lean_closure_set(v___f_5509_, 7, v_toBind_5494_);
    lean_closure_set(v___f_5509_, 8, v_setNextMacroScope_5495_);
    lean_closure_set(v___f_5509_, 9, v_inst_5496_);
    lean_closure_set(v___f_5509_, 10, v_inst_5497_);
    lean_closure_set(v___f_5509_, 11, v_inst_5498_);
    lean_closure_set(v___f_5509_, 12, v_toMonadRef_5481_);
    lean_closure_set(v___f_5509_, 13, v_inst_5499_);
    lean_closure_set(v___f_5509_, 14, v_inst_5500_);
    lean_closure_set(v___f_5509_, 15, v_toMonadExceptOf_5501_);
    lean_closure_set(v___f_5509_, 16, v_getNextMacroScope_5502_);
    v___x_5510_ = lean_apply_4(
        v_toBind_5494_,
        lean_box(0),
        lean_box(0),
        v_getRef_5504_,
        v___f_5509_,
    );
    return v___x_5510_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__19___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadRef_5511_: *mut LeanObject = *_args.add(0);
    let mut v_env_5512_: *mut LeanObject = *_args.add(1);
    let mut v_currNamespace_5513_: *mut LeanObject = *_args.add(2);
    let mut v_opts_5514_: *mut LeanObject = *_args.add(3);
    let mut v___x_5515_: *mut LeanObject = *_args.add(4);
    let mut v___f_5516_: *mut LeanObject = *_args.add(5);
    let mut v___f_5517_: *mut LeanObject = *_args.add(6);
    let mut v_toMonadQuotation_5518_: *mut LeanObject = *_args.add(7);
    let mut v_inst_5519_: *mut LeanObject = *_args.add(8);
    let mut v_x_5520_: *mut LeanObject = *_args.add(9);
    let mut v_toPure_5521_: *mut LeanObject = *_args.add(10);
    let mut v_inst_5522_: *mut LeanObject = *_args.add(11);
    let mut v___f_5523_: *mut LeanObject = *_args.add(12);
    let mut v_toBind_5524_: *mut LeanObject = *_args.add(13);
    let mut v_setNextMacroScope_5525_: *mut LeanObject = *_args.add(14);
    let mut v_inst_5526_: *mut LeanObject = *_args.add(15);
    let mut v_inst_5527_: *mut LeanObject = *_args.add(16);
    let mut v_inst_5528_: *mut LeanObject = *_args.add(17);
    let mut v_inst_5529_: *mut LeanObject = *_args.add(18);
    let mut v_inst_5530_: *mut LeanObject = *_args.add(19);
    let mut v_toMonadExceptOf_5531_: *mut LeanObject = *_args.add(20);
    let mut v_getNextMacroScope_5532_: *mut LeanObject = *_args.add(21);
    let mut v_openDecls_5533_: *mut LeanObject = *_args.add(22);
    let mut v_res_5534_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_toMonadRef_5535_: *mut LeanObject,
    mut v_env_5536_: *mut LeanObject,
    mut v_opts_5537_: *mut LeanObject,
    mut v___x_5538_: *mut LeanObject,
    mut v___f_5539_: *mut LeanObject,
    mut v___f_5540_: *mut LeanObject,
    mut v_toMonadQuotation_5541_: *mut LeanObject,
    mut v_inst_5542_: *mut LeanObject,
    mut v_x_5543_: *mut LeanObject,
    mut v_toPure_5544_: *mut LeanObject,
    mut v_inst_5545_: *mut LeanObject,
    mut v___f_5546_: *mut LeanObject,
    mut v_toBind_5547_: *mut LeanObject,
    mut v_setNextMacroScope_5548_: *mut LeanObject,
    mut v_inst_5549_: *mut LeanObject,
    mut v_inst_5550_: *mut LeanObject,
    mut v_inst_5551_: *mut LeanObject,
    mut v_inst_5552_: *mut LeanObject,
    mut v_inst_5553_: *mut LeanObject,
    mut v_toMonadExceptOf_5554_: *mut LeanObject,
    mut v_getNextMacroScope_5555_: *mut LeanObject,
    mut v_getOpenDecls_5556_: *mut LeanObject,
    mut v_currNamespace_5557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_5547_);
    v___f_5558_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__19___boxed as *mut core::ffi::c_void,
        23,
        22,
    );
    lean_closure_set(v___f_5558_, 0, v_toMonadRef_5535_);
    lean_closure_set(v___f_5558_, 1, v_env_5536_);
    lean_closure_set(v___f_5558_, 2, v_currNamespace_5557_);
    lean_closure_set(v___f_5558_, 3, v_opts_5537_);
    lean_closure_set(v___f_5558_, 4, v___x_5538_);
    lean_closure_set(v___f_5558_, 5, v___f_5539_);
    lean_closure_set(v___f_5558_, 6, v___f_5540_);
    lean_closure_set(v___f_5558_, 7, v_toMonadQuotation_5541_);
    lean_closure_set(v___f_5558_, 8, v_inst_5542_);
    lean_closure_set(v___f_5558_, 9, v_x_5543_);
    lean_closure_set(v___f_5558_, 10, v_toPure_5544_);
    lean_closure_set(v___f_5558_, 11, v_inst_5545_);
    lean_closure_set(v___f_5558_, 12, v___f_5546_);
    lean_closure_set(v___f_5558_, 13, v_toBind_5547_);
    lean_closure_set(v___f_5558_, 14, v_setNextMacroScope_5548_);
    lean_closure_set(v___f_5558_, 15, v_inst_5549_);
    lean_closure_set(v___f_5558_, 16, v_inst_5550_);
    lean_closure_set(v___f_5558_, 17, v_inst_5551_);
    lean_closure_set(v___f_5558_, 18, v_inst_5552_);
    lean_closure_set(v___f_5558_, 19, v_inst_5553_);
    lean_closure_set(v___f_5558_, 20, v_toMonadExceptOf_5554_);
    lean_closure_set(v___f_5558_, 21, v_getNextMacroScope_5555_);
    v___x_5559_ = lean_apply_4(
        v_toBind_5547_,
        lean_box(0),
        lean_box(0),
        v_getOpenDecls_5556_,
        v___f_5558_,
    );
    return v___x_5559_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__20___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadRef_5560_: *mut LeanObject = *_args.add(0);
    let mut v_env_5561_: *mut LeanObject = *_args.add(1);
    let mut v_opts_5562_: *mut LeanObject = *_args.add(2);
    let mut v___x_5563_: *mut LeanObject = *_args.add(3);
    let mut v___f_5564_: *mut LeanObject = *_args.add(4);
    let mut v___f_5565_: *mut LeanObject = *_args.add(5);
    let mut v_toMonadQuotation_5566_: *mut LeanObject = *_args.add(6);
    let mut v_inst_5567_: *mut LeanObject = *_args.add(7);
    let mut v_x_5568_: *mut LeanObject = *_args.add(8);
    let mut v_toPure_5569_: *mut LeanObject = *_args.add(9);
    let mut v_inst_5570_: *mut LeanObject = *_args.add(10);
    let mut v___f_5571_: *mut LeanObject = *_args.add(11);
    let mut v_toBind_5572_: *mut LeanObject = *_args.add(12);
    let mut v_setNextMacroScope_5573_: *mut LeanObject = *_args.add(13);
    let mut v_inst_5574_: *mut LeanObject = *_args.add(14);
    let mut v_inst_5575_: *mut LeanObject = *_args.add(15);
    let mut v_inst_5576_: *mut LeanObject = *_args.add(16);
    let mut v_inst_5577_: *mut LeanObject = *_args.add(17);
    let mut v_inst_5578_: *mut LeanObject = *_args.add(18);
    let mut v_toMonadExceptOf_5579_: *mut LeanObject = *_args.add(19);
    let mut v_getNextMacroScope_5580_: *mut LeanObject = *_args.add(20);
    let mut v_getOpenDecls_5581_: *mut LeanObject = *_args.add(21);
    let mut v_currNamespace_5582_: *mut LeanObject = *_args.add(22);
    let mut v_res_5583_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_5584_: *mut LeanObject,
    mut v_toMonadRef_5585_: *mut LeanObject,
    mut v_env_5586_: *mut LeanObject,
    mut v___x_5587_: *mut LeanObject,
    mut v___f_5588_: *mut LeanObject,
    mut v___f_5589_: *mut LeanObject,
    mut v_toMonadQuotation_5590_: *mut LeanObject,
    mut v_inst_5591_: *mut LeanObject,
    mut v_x_5592_: *mut LeanObject,
    mut v_toPure_5593_: *mut LeanObject,
    mut v_inst_5594_: *mut LeanObject,
    mut v___f_5595_: *mut LeanObject,
    mut v_toBind_5596_: *mut LeanObject,
    mut v_setNextMacroScope_5597_: *mut LeanObject,
    mut v_inst_5598_: *mut LeanObject,
    mut v_inst_5599_: *mut LeanObject,
    mut v_inst_5600_: *mut LeanObject,
    mut v_inst_5601_: *mut LeanObject,
    mut v_inst_5602_: *mut LeanObject,
    mut v_toMonadExceptOf_5603_: *mut LeanObject,
    mut v_getNextMacroScope_5604_: *mut LeanObject,
    mut v_opts_5605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getCurrNamespace_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    v_getCurrNamespace_5606_ = lean_ctor_get(v_inst_5584_, 0);
    lean_inc(v_getCurrNamespace_5606_);
    v_getOpenDecls_5607_ = lean_ctor_get(v_inst_5584_, 1);
    lean_inc(v_getOpenDecls_5607_);
    lean_dec_ref(v_inst_5584_);
    lean_inc(v_toBind_5596_);
    v___f_5608_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__20___boxed as *mut core::ffi::c_void,
        23,
        22,
    );
    lean_closure_set(v___f_5608_, 0, v_toMonadRef_5585_);
    lean_closure_set(v___f_5608_, 1, v_env_5586_);
    lean_closure_set(v___f_5608_, 2, v_opts_5605_);
    lean_closure_set(v___f_5608_, 3, v___x_5587_);
    lean_closure_set(v___f_5608_, 4, v___f_5588_);
    lean_closure_set(v___f_5608_, 5, v___f_5589_);
    lean_closure_set(v___f_5608_, 6, v_toMonadQuotation_5590_);
    lean_closure_set(v___f_5608_, 7, v_inst_5591_);
    lean_closure_set(v___f_5608_, 8, v_x_5592_);
    lean_closure_set(v___f_5608_, 9, v_toPure_5593_);
    lean_closure_set(v___f_5608_, 10, v_inst_5594_);
    lean_closure_set(v___f_5608_, 11, v___f_5595_);
    lean_closure_set(v___f_5608_, 12, v_toBind_5596_);
    lean_closure_set(v___f_5608_, 13, v_setNextMacroScope_5597_);
    lean_closure_set(v___f_5608_, 14, v_inst_5598_);
    lean_closure_set(v___f_5608_, 15, v_inst_5599_);
    lean_closure_set(v___f_5608_, 16, v_inst_5600_);
    lean_closure_set(v___f_5608_, 17, v_inst_5601_);
    lean_closure_set(v___f_5608_, 18, v_inst_5602_);
    lean_closure_set(v___f_5608_, 19, v_toMonadExceptOf_5603_);
    lean_closure_set(v___f_5608_, 20, v_getNextMacroScope_5604_);
    lean_closure_set(v___f_5608_, 21, v_getOpenDecls_5607_);
    v___x_5609_ = lean_apply_4(
        v_toBind_5596_,
        lean_box(0),
        lean_box(0),
        v_getCurrNamespace_5606_,
        v___f_5608_,
    );
    return v___x_5609_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__21___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_5610_: *mut LeanObject = *_args.add(0);
    let mut v_toMonadRef_5611_: *mut LeanObject = *_args.add(1);
    let mut v_env_5612_: *mut LeanObject = *_args.add(2);
    let mut v___x_5613_: *mut LeanObject = *_args.add(3);
    let mut v___f_5614_: *mut LeanObject = *_args.add(4);
    let mut v___f_5615_: *mut LeanObject = *_args.add(5);
    let mut v_toMonadQuotation_5616_: *mut LeanObject = *_args.add(6);
    let mut v_inst_5617_: *mut LeanObject = *_args.add(7);
    let mut v_x_5618_: *mut LeanObject = *_args.add(8);
    let mut v_toPure_5619_: *mut LeanObject = *_args.add(9);
    let mut v_inst_5620_: *mut LeanObject = *_args.add(10);
    let mut v___f_5621_: *mut LeanObject = *_args.add(11);
    let mut v_toBind_5622_: *mut LeanObject = *_args.add(12);
    let mut v_setNextMacroScope_5623_: *mut LeanObject = *_args.add(13);
    let mut v_inst_5624_: *mut LeanObject = *_args.add(14);
    let mut v_inst_5625_: *mut LeanObject = *_args.add(15);
    let mut v_inst_5626_: *mut LeanObject = *_args.add(16);
    let mut v_inst_5627_: *mut LeanObject = *_args.add(17);
    let mut v_inst_5628_: *mut LeanObject = *_args.add(18);
    let mut v_toMonadExceptOf_5629_: *mut LeanObject = *_args.add(19);
    let mut v_getNextMacroScope_5630_: *mut LeanObject = *_args.add(20);
    let mut v_opts_5631_: *mut LeanObject = *_args.add(21);
    let mut v_res_5632_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_5633_: *mut LeanObject,
    mut v___x_5634_: *mut LeanObject,
    mut v_inst_5635_: *mut LeanObject,
    mut v_toMonadRef_5636_: *mut LeanObject,
    mut v___x_5637_: *mut LeanObject,
    mut v_toMonadQuotation_5638_: *mut LeanObject,
    mut v_inst_5639_: *mut LeanObject,
    mut v_x_5640_: *mut LeanObject,
    mut v_toPure_5641_: *mut LeanObject,
    mut v_inst_5642_: *mut LeanObject,
    mut v___f_5643_: *mut LeanObject,
    mut v_toBind_5644_: *mut LeanObject,
    mut v_setNextMacroScope_5645_: *mut LeanObject,
    mut v_inst_5646_: *mut LeanObject,
    mut v_inst_5647_: *mut LeanObject,
    mut v_inst_5648_: *mut LeanObject,
    mut v_inst_5649_: *mut LeanObject,
    mut v_inst_5650_: *mut LeanObject,
    mut v_toMonadExceptOf_5651_: *mut LeanObject,
    mut v_getNextMacroScope_5652_: *mut LeanObject,
    mut v_env_5653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_env_5653_, 2);
    v___f_5654_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__4___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_5654_, 0, v_env_5653_);
    lean_closure_set(v___f_5654_, 1, v___x_5633_);
    lean_closure_set(v___f_5654_, 2, v___x_5634_);
    v___f_5655_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__5___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5655_, 0, v_env_5653_);
    lean_inc(v_inst_5648_);
    lean_inc(v_toBind_5644_);
    v___f_5656_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__21___boxed as *mut core::ffi::c_void,
        22,
        21,
    );
    lean_closure_set(v___f_5656_, 0, v_inst_5635_);
    lean_closure_set(v___f_5656_, 1, v_toMonadRef_5636_);
    lean_closure_set(v___f_5656_, 2, v_env_5653_);
    lean_closure_set(v___f_5656_, 3, v___x_5637_);
    lean_closure_set(v___f_5656_, 4, v___f_5654_);
    lean_closure_set(v___f_5656_, 5, v___f_5655_);
    lean_closure_set(v___f_5656_, 6, v_toMonadQuotation_5638_);
    lean_closure_set(v___f_5656_, 7, v_inst_5639_);
    lean_closure_set(v___f_5656_, 8, v_x_5640_);
    lean_closure_set(v___f_5656_, 9, v_toPure_5641_);
    lean_closure_set(v___f_5656_, 10, v_inst_5642_);
    lean_closure_set(v___f_5656_, 11, v___f_5643_);
    lean_closure_set(v___f_5656_, 12, v_toBind_5644_);
    lean_closure_set(v___f_5656_, 13, v_setNextMacroScope_5645_);
    lean_closure_set(v___f_5656_, 14, v_inst_5646_);
    lean_closure_set(v___f_5656_, 15, v_inst_5647_);
    lean_closure_set(v___f_5656_, 16, v_inst_5648_);
    lean_closure_set(v___f_5656_, 17, v_inst_5649_);
    lean_closure_set(v___f_5656_, 18, v_inst_5650_);
    lean_closure_set(v___f_5656_, 19, v_toMonadExceptOf_5651_);
    lean_closure_set(v___f_5656_, 20, v_getNextMacroScope_5652_);
    v___x_5657_ = lean_apply_4(
        v_toBind_5644_,
        lean_box(0),
        lean_box(0),
        v_inst_5648_,
        v___f_5656_,
    );
    return v___x_5657_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg___lam__22___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5658_: *mut LeanObject = *_args.add(0);
    let mut v___x_5659_: *mut LeanObject = *_args.add(1);
    let mut v_inst_5660_: *mut LeanObject = *_args.add(2);
    let mut v_toMonadRef_5661_: *mut LeanObject = *_args.add(3);
    let mut v___x_5662_: *mut LeanObject = *_args.add(4);
    let mut v_toMonadQuotation_5663_: *mut LeanObject = *_args.add(5);
    let mut v_inst_5664_: *mut LeanObject = *_args.add(6);
    let mut v_x_5665_: *mut LeanObject = *_args.add(7);
    let mut v_toPure_5666_: *mut LeanObject = *_args.add(8);
    let mut v_inst_5667_: *mut LeanObject = *_args.add(9);
    let mut v___f_5668_: *mut LeanObject = *_args.add(10);
    let mut v_toBind_5669_: *mut LeanObject = *_args.add(11);
    let mut v_setNextMacroScope_5670_: *mut LeanObject = *_args.add(12);
    let mut v_inst_5671_: *mut LeanObject = *_args.add(13);
    let mut v_inst_5672_: *mut LeanObject = *_args.add(14);
    let mut v_inst_5673_: *mut LeanObject = *_args.add(15);
    let mut v_inst_5674_: *mut LeanObject = *_args.add(16);
    let mut v_inst_5675_: *mut LeanObject = *_args.add(17);
    let mut v_toMonadExceptOf_5676_: *mut LeanObject = *_args.add(18);
    let mut v_getNextMacroScope_5677_: *mut LeanObject = *_args.add(19);
    let mut v_env_5678_: *mut LeanObject = *_args.add(20);
    let mut v_res_5679_: *mut LeanObject = core::ptr::null_mut();
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
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    v___x_5699_ = l_EStateM_nonBacktrackable(lean_box(0));
    return v___x_5699_;
}
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__11() -> *mut LeanObject {
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    v___x_5700_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__10_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__10,
    );
    v___x_5701_ = l_EStateM_instMonadExceptOfOfBacktrackable___redArg(v___x_5700_);
    return v___x_5701_;
}
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__12() -> *mut LeanObject {
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5703_: *mut LeanObject = core::ptr::null_mut();
    v___x_5702_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__11_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__11,
    );
    v___f_5703_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5703_, 0, v___x_5702_);
    return v___f_5703_;
}
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__13() -> *mut LeanObject {
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5705_: *mut LeanObject = core::ptr::null_mut();
    v___x_5704_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__11_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__11,
    );
    v___f_5705_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5705_, 0, v___x_5704_);
    return v___f_5705_;
}
pub unsafe fn _init_l_Lean_Elab_liftMacroM___redArg___closed__14() -> *mut LeanObject {
    let mut v___f_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    v___f_5706_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__13_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__13,
    );
    v___f_5707_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__12_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__12,
    );
    v___x_5708_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5708_, 0, v___f_5707_);
    lean_ctor_set(v___x_5708_, 1, v___f_5706_);
    return v___x_5708_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___redArg(
    mut v_inst_5711_: *mut LeanObject,
    mut v_inst_5712_: *mut LeanObject,
    mut v_inst_5713_: *mut LeanObject,
    mut v_inst_5714_: *mut LeanObject,
    mut v_inst_5715_: *mut LeanObject,
    mut v_inst_5716_: *mut LeanObject,
    mut v_inst_5717_: *mut LeanObject,
    mut v_inst_5718_: *mut LeanObject,
    mut v_inst_5719_: *mut LeanObject,
    mut v_x_5720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadExceptOf_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadQuotation_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getNextMacroScope_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_setNextMacroScope_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    v___x_5721_ = l_Lean_Elab_liftMacroM___redArg___closed__9;
    v___x_5722_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Elab_liftMacroM___redArg___closed__14_once),
        _init_l_Lean_Elab_liftMacroM___redArg___closed__14,
    );
    v_toApplicative_5723_ = lean_ctor_get(v_inst_5711_, 0);
    v_toBind_5724_ = lean_ctor_get(v_inst_5711_, 1);
    lean_inc_n(v_toBind_5724_, 3);
    v_getEnv_5725_ = lean_ctor_get(v_inst_5713_, 0);
    lean_inc(v_getEnv_5725_);
    v_toMonadExceptOf_5726_ = lean_ctor_get(v_inst_5715_, 0);
    lean_inc_ref(v_toMonadExceptOf_5726_);
    v_toMonadRef_5727_ = lean_ctor_get(v_inst_5715_, 1);
    lean_inc_ref_n(v_toMonadRef_5727_, 2);
    v_toMonadQuotation_5728_ = lean_ctor_get(v_inst_5712_, 0);
    lean_inc_ref(v_toMonadQuotation_5728_);
    v_getNextMacroScope_5729_ = lean_ctor_get(v_inst_5712_, 1);
    lean_inc(v_getNextMacroScope_5729_);
    v_setNextMacroScope_5730_ = lean_ctor_get(v_inst_5712_, 2);
    lean_inc(v_setNextMacroScope_5730_);
    lean_dec_ref(v_inst_5712_);
    v_toPure_5731_ = lean_ctor_get(v_toApplicative_5723_, 1);
    lean_inc_n(v_toPure_5731_, 2);
    v___x_5732_ = l_Lean_Elab_liftMacroM___redArg___closed__15;
    lean_inc(v_inst_5718_);
    lean_inc(v_inst_5719_);
    lean_inc_ref(v_inst_5711_);
    lean_inc_ref(v_inst_5717_);
    v___f_5733_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_5733_, 0, v_inst_5717_);
    lean_closure_set(v___f_5733_, 1, v_toPure_5731_);
    lean_closure_set(v___f_5733_, 2, v_inst_5711_);
    lean_closure_set(v___f_5733_, 3, v_toMonadRef_5727_);
    lean_closure_set(v___f_5733_, 4, v_inst_5719_);
    lean_closure_set(v___f_5733_, 5, v_toBind_5724_);
    lean_closure_set(v___f_5733_, 6, v_inst_5718_);
    v___f_5734_ = lean_alloc_closure(
        l_Lean_Elab_liftMacroM___redArg___lam__22___boxed as *mut core::ffi::c_void,
        21,
        20,
    );
    lean_closure_set(v___f_5734_, 0, v___x_5722_);
    lean_closure_set(v___f_5734_, 1, v___x_5732_);
    lean_closure_set(v___f_5734_, 2, v_inst_5716_);
    lean_closure_set(v___f_5734_, 3, v_toMonadRef_5727_);
    lean_closure_set(v___f_5734_, 4, v___x_5721_);
    lean_closure_set(v___f_5734_, 5, v_toMonadQuotation_5728_);
    lean_closure_set(v___f_5734_, 6, v_inst_5714_);
    lean_closure_set(v___f_5734_, 7, v_x_5720_);
    lean_closure_set(v___f_5734_, 8, v_toPure_5731_);
    lean_closure_set(v___f_5734_, 9, v_inst_5711_);
    lean_closure_set(v___f_5734_, 10, v___f_5733_);
    lean_closure_set(v___f_5734_, 11, v_toBind_5724_);
    lean_closure_set(v___f_5734_, 12, v_setNextMacroScope_5730_);
    lean_closure_set(v___f_5734_, 13, v_inst_5713_);
    lean_closure_set(v___f_5734_, 14, v_inst_5717_);
    lean_closure_set(v___f_5734_, 15, v_inst_5718_);
    lean_closure_set(v___f_5734_, 16, v_inst_5719_);
    lean_closure_set(v___f_5734_, 17, v_inst_5715_);
    lean_closure_set(v___f_5734_, 18, v_toMonadExceptOf_5726_);
    lean_closure_set(v___f_5734_, 19, v_getNextMacroScope_5729_);
    v___x_5735_ = lean_apply_4(
        v_toBind_5724_,
        lean_box(0),
        lean_box(0),
        v_getEnv_5725_,
        v___f_5734_,
    );
    return v___x_5735_;
}
pub unsafe fn l_Lean_Elab_liftMacroM(
    mut v_m_5736_: *mut LeanObject,
    mut v_00_u03b1_5737_: *mut LeanObject,
    mut v_inst_5738_: *mut LeanObject,
    mut v_inst_5739_: *mut LeanObject,
    mut v_inst_5740_: *mut LeanObject,
    mut v_inst_5741_: *mut LeanObject,
    mut v_inst_5742_: *mut LeanObject,
    mut v_inst_5743_: *mut LeanObject,
    mut v_inst_5744_: *mut LeanObject,
    mut v_inst_5745_: *mut LeanObject,
    mut v_inst_5746_: *mut LeanObject,
    mut v_inst_5747_: *mut LeanObject,
    mut v_x_5748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_5750_: *mut LeanObject,
    mut v_00_u03b1_5751_: *mut LeanObject,
    mut v_inst_5752_: *mut LeanObject,
    mut v_inst_5753_: *mut LeanObject,
    mut v_inst_5754_: *mut LeanObject,
    mut v_inst_5755_: *mut LeanObject,
    mut v_inst_5756_: *mut LeanObject,
    mut v_inst_5757_: *mut LeanObject,
    mut v_inst_5758_: *mut LeanObject,
    mut v_inst_5759_: *mut LeanObject,
    mut v_inst_5760_: *mut LeanObject,
    mut v_inst_5761_: *mut LeanObject,
    mut v_x_5762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5763_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_5761_);
    return v_res_5763_;
}
pub unsafe fn l_Lean_Elab_adaptMacro___redArg(
    mut v_inst_5764_: *mut LeanObject,
    mut v_inst_5765_: *mut LeanObject,
    mut v_inst_5766_: *mut LeanObject,
    mut v_inst_5767_: *mut LeanObject,
    mut v_inst_5768_: *mut LeanObject,
    mut v_inst_5769_: *mut LeanObject,
    mut v_inst_5770_: *mut LeanObject,
    mut v_inst_5771_: *mut LeanObject,
    mut v_inst_5772_: *mut LeanObject,
    mut v_x_5773_: *mut LeanObject,
    mut v_stx_5774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    v___x_5775_ = lean_apply_1(v_x_5773_, v_stx_5774_);
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
    mut v_m_5777_: *mut LeanObject,
    mut v_inst_5778_: *mut LeanObject,
    mut v_inst_5779_: *mut LeanObject,
    mut v_inst_5780_: *mut LeanObject,
    mut v_inst_5781_: *mut LeanObject,
    mut v_inst_5782_: *mut LeanObject,
    mut v_inst_5783_: *mut LeanObject,
    mut v_inst_5784_: *mut LeanObject,
    mut v_inst_5785_: *mut LeanObject,
    mut v_inst_5786_: *mut LeanObject,
    mut v_inst_5787_: *mut LeanObject,
    mut v_x_5788_: *mut LeanObject,
    mut v_stx_5789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    v___x_5790_ = lean_apply_1(v_x_5788_, v_stx_5789_);
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
    mut v_m_5792_: *mut LeanObject,
    mut v_inst_5793_: *mut LeanObject,
    mut v_inst_5794_: *mut LeanObject,
    mut v_inst_5795_: *mut LeanObject,
    mut v_inst_5796_: *mut LeanObject,
    mut v_inst_5797_: *mut LeanObject,
    mut v_inst_5798_: *mut LeanObject,
    mut v_inst_5799_: *mut LeanObject,
    mut v_inst_5800_: *mut LeanObject,
    mut v_inst_5801_: *mut LeanObject,
    mut v_inst_5802_: *mut LeanObject,
    mut v_x_5803_: *mut LeanObject,
    mut v_stx_5804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5805_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_5802_);
    return v_res_5805_;
}
pub unsafe fn l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(
    mut v_baseName_5806_: *mut LeanObject,
    mut v_currNamespace_5807_: *mut LeanObject,
    mut v_idx_5808_: *mut LeanObject,
    mut v_a_5809_: *mut LeanObject,
    mut v_a_5810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: u8 = 0;
    let mut v_a_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5823_: u8 = 0;
    let mut v_unused_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5833_: u8 = 0;
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_idx_5808_);
                lean_inc(v_baseName_5806_);
                v_name_5811_ = lean_name_append_index_after(v_baseName_5806_, v_idx_5808_);
                lean_inc(v_name_5811_);
                lean_inc(v_currNamespace_5807_);
                v___x_5812_ = l_Lean_Name_append(v_currNamespace_5807_, v_name_5811_);
                v___x_5813_ = l_Lean_Macro_hasDecl(v___x_5812_, v_a_5809_, v_a_5810_);
                if lean_obj_tag(v___x_5813_) == 0 {
                    v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
                    lean_inc(v_a_5814_);
                    v___x_5815_ = (lean_unbox(v_a_5814_) as u8);
                    lean_dec(v_a_5814_);
                    if v___x_5815_ == 0 {
                        lean_dec(v_idx_5808_);
                        lean_dec(v_currNamespace_5807_);
                        lean_dec(v_baseName_5806_);
                        v_a_5816_ = lean_ctor_get(v___x_5813_, 1);
                        v_isSharedCheck_5823_ = (!lean_is_exclusive(v___x_5813_)) as u8;
                        if v_isSharedCheck_5823_ == 0 {
                            v_unused_5824_ = lean_ctor_get(v___x_5813_, 0);
                            lean_dec(v_unused_5824_);
                            v___x_5818_ = v___x_5813_;
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5816_);
                            lean_dec(v___x_5813_);
                            v___x_5818_ = lean_box(0);
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_name_5811_);
                        v_a_5825_ = lean_ctor_get(v___x_5813_, 1);
                        lean_inc(v_a_5825_);
                        lean_dec_ref_known(v___x_5813_, 2);
                        v___x_5826_ = lean_unsigned_to_nat(1);
                        v___x_5827_ = lean_nat_add(v_idx_5808_, v___x_5826_);
                        lean_dec(v_idx_5808_);
                        v_idx_5808_ = v___x_5827_;
                        v_a_5810_ = v_a_5825_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_name_5811_);
                    lean_dec(v_idx_5808_);
                    lean_dec(v_currNamespace_5807_);
                    lean_dec(v_baseName_5806_);
                    v_a_5829_ = lean_ctor_get(v___x_5813_, 0);
                    v_a_5830_ = lean_ctor_get(v___x_5813_, 1);
                    v_isSharedCheck_5837_ = (!lean_is_exclusive(v___x_5813_)) as u8;
                    if v_isSharedCheck_5837_ == 0 {
                        v___x_5832_ = v___x_5813_;
                        v_isShared_5833_ = v_isSharedCheck_5837_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5830_);
                        lean_inc(v_a_5829_);
                        lean_dec(v___x_5813_);
                        v___x_5832_ = lean_box(0);
                        v_isShared_5833_ = v_isSharedCheck_5837_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5819_ == 0 {
                    lean_ctor_set(v___x_5818_, 0, v_name_5811_);
                    v___x_5821_ = v___x_5818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5822_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_name_5811_);
                    lean_ctor_set(v_reuseFailAlloc_5822_, 1, v_a_5816_);
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
                    v_reuseFailAlloc_5836_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_a_5829_);
                    lean_ctor_set(v_reuseFailAlloc_5836_, 1, v_a_5830_);
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
    mut v_baseName_5838_: *mut LeanObject,
    mut v_currNamespace_5839_: *mut LeanObject,
    mut v_idx_5840_: *mut LeanObject,
    mut v_a_5841_: *mut LeanObject,
    mut v_a_5842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5843_: *mut LeanObject = core::ptr::null_mut();
    v_res_5843_ = l___private_Lean_Elab_Util_0__Lean_Elab_mkUnusedBaseName_loop(
        v_baseName_5838_,
        v_currNamespace_5839_,
        v_idx_5840_,
        v_a_5841_,
        v_a_5842_,
    );
    lean_dec_ref(v_a_5841_);
    return v_res_5843_;
}
pub unsafe fn l_Lean_Elab_mkUnusedBaseName(
    mut v_baseName_5844_: *mut LeanObject,
    mut v_a_5845_: *mut LeanObject,
    mut v_a_5846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: u8 = 0;
    let mut v_a_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5857_: u8 = 0;
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5861_: u8 = 0;
    let mut v_unused_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5870_: u8 = 0;
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5847_ = l_Lean_Macro_getCurrNamespace(v_a_5845_, v_a_5846_);
                if lean_obj_tag(v___x_5847_) == 0 {
                    v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
                    lean_inc_n(v_a_5848_, 2);
                    v_a_5849_ = lean_ctor_get(v___x_5847_, 1);
                    lean_inc(v_a_5849_);
                    lean_dec_ref_known(v___x_5847_, 2);
                    lean_inc(v_baseName_5844_);
                    v___x_5850_ = l_Lean_Name_append(v_a_5848_, v_baseName_5844_);
                    v___x_5851_ = l_Lean_Macro_hasDecl(v___x_5850_, v_a_5845_, v_a_5849_);
                    if lean_obj_tag(v___x_5851_) == 0 {
                        v_a_5852_ = lean_ctor_get(v___x_5851_, 0);
                        lean_inc(v_a_5852_);
                        v___x_5853_ = (lean_unbox(v_a_5852_) as u8);
                        lean_dec(v_a_5852_);
                        if v___x_5853_ == 0 {
                            lean_dec(v_a_5848_);
                            v_a_5854_ = lean_ctor_get(v___x_5851_, 1);
                            v_isSharedCheck_5861_ = (!lean_is_exclusive(v___x_5851_)) as u8;
                            if v_isSharedCheck_5861_ == 0 {
                                v_unused_5862_ = lean_ctor_get(v___x_5851_, 0);
                                lean_dec(v_unused_5862_);
                                v___x_5856_ = v___x_5851_;
                                v_isShared_5857_ = v_isSharedCheck_5861_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5854_);
                                lean_dec(v___x_5851_);
                                v___x_5856_ = lean_box(0);
                                v_isShared_5857_ = v_isSharedCheck_5861_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_5863_ = lean_ctor_get(v___x_5851_, 1);
                            lean_inc(v_a_5863_);
                            lean_dec_ref_known(v___x_5851_, 2);
                            v___x_5864_ = lean_unsigned_to_nat(1);
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
                        lean_dec(v_a_5848_);
                        lean_dec(v_baseName_5844_);
                        v_a_5866_ = lean_ctor_get(v___x_5851_, 0);
                        v_a_5867_ = lean_ctor_get(v___x_5851_, 1);
                        v_isSharedCheck_5874_ = (!lean_is_exclusive(v___x_5851_)) as u8;
                        if v_isSharedCheck_5874_ == 0 {
                            v___x_5869_ = v___x_5851_;
                            v_isShared_5870_ = v_isSharedCheck_5874_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5867_);
                            lean_inc(v_a_5866_);
                            lean_dec(v___x_5851_);
                            v___x_5869_ = lean_box(0);
                            v_isShared_5870_ = v_isSharedCheck_5874_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_baseName_5844_);
                    return v___x_5847_;
                }
            }
            1 => {
                if v_isShared_5857_ == 0 {
                    lean_ctor_set(v___x_5856_, 0, v_baseName_5844_);
                    v___x_5859_ = v___x_5856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5860_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_baseName_5844_);
                    lean_ctor_set(v_reuseFailAlloc_5860_, 1, v_a_5854_);
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
                    v_reuseFailAlloc_5873_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5866_);
                    lean_ctor_set(v_reuseFailAlloc_5873_, 1, v_a_5867_);
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
    mut v_baseName_5875_: *mut LeanObject,
    mut v_a_5876_: *mut LeanObject,
    mut v_a_5877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5878_: *mut LeanObject = core::ptr::null_mut();
    v_res_5878_ = l_Lean_Elab_mkUnusedBaseName(v_baseName_5875_, v_a_5876_, v_a_5877_);
    lean_dec_ref(v_a_5876_);
    return v_res_5878_;
}
pub unsafe fn _init_l_Lean_Elab_logException___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    v___x_5880_ = l_Lean_Elab_logException___redArg___lam__0___closed__0;
    v___x_5881_ = l_Lean_stringToMessageData(v___x_5880_);
    return v___x_5881_;
}
pub unsafe fn l_Lean_Elab_logException___redArg___lam__0(
    mut v_inst_5882_: *mut LeanObject,
    mut v_inst_5883_: *mut LeanObject,
    mut v_inst_5884_: *mut LeanObject,
    mut v_inst_5885_: *mut LeanObject,
    mut v_name_5886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    v___x_5887_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_logException___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_logException___redArg___lam__0___closed__1_once),
        _init_l_Lean_Elab_logException___redArg___lam__0___closed__1,
    );
    v___x_5888_ = l_Lean_MessageData_ofName(v_name_5886_);
    v___x_5889_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5889_, 0, v___x_5887_);
    lean_ctor_set(v___x_5889_, 1, v___x_5888_);
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
    mut v_inst_5891_: *mut LeanObject,
    mut v_inst_5892_: *mut LeanObject,
    mut v_inst_5893_: *mut LeanObject,
    mut v_inst_5894_: *mut LeanObject,
    mut v_inst_5895_: *mut LeanObject,
    mut v_ex_5896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5903_: u8 = 0;
    let mut v_toBind_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: u8 = 0;
    let mut v___x_5913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_ex_5896_) == 0 {
                    lean_dec(v_inst_5895_);
                    v_ref_5897_ = lean_ctor_get(v_ex_5896_, 0);
                    lean_inc(v_ref_5897_);
                    v_msg_5898_ = lean_ctor_get(v_ex_5896_, 1);
                    lean_inc_ref(v_msg_5898_);
                    lean_dec_ref_known(v_ex_5896_, 2);
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
                    v_id_5900_ = lean_ctor_get(v_ex_5896_, 0);
                    lean_inc(v_id_5900_);
                    lean_inc_ref(v_inst_5891_);
                    v___f_5901_ = lean_alloc_closure(
                        l_Lean_Elab_logException___redArg___lam__0 as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    lean_closure_set(v___f_5901_, 0, v_inst_5891_);
                    lean_closure_set(v___f_5901_, 1, v_inst_5892_);
                    lean_closure_set(v___f_5901_, 2, v_inst_5893_);
                    lean_closure_set(v___f_5901_, 3, v_inst_5894_);
                    v___x_5912_ = l_Lean_Elab_isAbortExceptionId(v_id_5900_);
                    if v___x_5912_ == 0 {
                        v___x_5913_ = l_Lean_Exception_isInterrupt(v_ex_5896_);
                        lean_dec_ref_known(v_ex_5896_, 2);
                        v___y_5903_ = v___x_5913_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref_known(v_ex_5896_, 2);
                        v___y_5903_ = v___x_5912_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5903_ == 0 {
                    v_toBind_5904_ = lean_ctor_get(v_inst_5891_, 1);
                    lean_inc(v_toBind_5904_);
                    lean_dec_ref(v_inst_5891_);
                    v___x_5905_ = lean_alloc_closure(
                        l_Lean_InternalExceptionId_getName___boxed as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___x_5905_, 0, v_id_5900_);
                    v___x_5906_ = lean_apply_2(v_inst_5895_, lean_box(0), v___x_5905_);
                    v___x_5907_ = lean_apply_4(
                        v_toBind_5904_,
                        lean_box(0),
                        lean_box(0),
                        v___x_5906_,
                        v___f_5901_,
                    );
                    return v___x_5907_;
                } else {
                    lean_dec_ref(v___f_5901_);
                    lean_dec(v_id_5900_);
                    lean_dec(v_inst_5895_);
                    v_toApplicative_5908_ = lean_ctor_get(v_inst_5891_, 0);
                    lean_inc_ref(v_toApplicative_5908_);
                    lean_dec_ref(v_inst_5891_);
                    v_toPure_5909_ = lean_ctor_get(v_toApplicative_5908_, 1);
                    lean_inc(v_toPure_5909_);
                    lean_dec_ref(v_toApplicative_5908_);
                    v___x_5910_ = lean_box(0);
                    v___x_5911_ = lean_apply_2(v_toPure_5909_, lean_box(0), v___x_5910_);
                    return v___x_5911_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_logException(
    mut v_m_5914_: *mut LeanObject,
    mut v_inst_5915_: *mut LeanObject,
    mut v_inst_5916_: *mut LeanObject,
    mut v_inst_5917_: *mut LeanObject,
    mut v_inst_5918_: *mut LeanObject,
    mut v_inst_5919_: *mut LeanObject,
    mut v_ex_5920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_5922_: *mut LeanObject,
    mut v_inst_5923_: *mut LeanObject,
    mut v_inst_5924_: *mut LeanObject,
    mut v_inst_5925_: *mut LeanObject,
    mut v_inst_5926_: *mut LeanObject,
    mut v_ex_5927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_5929_: *mut LeanObject,
    mut v_inst_5930_: *mut LeanObject,
    mut v_inst_5931_: *mut LeanObject,
    mut v_inst_5932_: *mut LeanObject,
    mut v_inst_5933_: *mut LeanObject,
    mut v_inst_5934_: *mut LeanObject,
    mut v_x_5935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_5936_ = lean_ctor_get(v_inst_5931_, 1);
    lean_inc(v_tryCatch_5936_);
    lean_dec_ref(v_inst_5931_);
    v___f_5937_ = lean_alloc_closure(
        l_Lean_Elab_withLogging___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_5937_, 0, v_inst_5929_);
    lean_closure_set(v___f_5937_, 1, v_inst_5930_);
    lean_closure_set(v___f_5937_, 2, v_inst_5932_);
    lean_closure_set(v___f_5937_, 3, v_inst_5933_);
    lean_closure_set(v___f_5937_, 4, v_inst_5934_);
    v___x_5938_ = lean_apply_3(v_tryCatch_5936_, lean_box(0), v_x_5935_, v___f_5937_);
    return v___x_5938_;
}
pub unsafe fn l_Lean_Elab_withLogging(
    mut v_m_5939_: *mut LeanObject,
    mut v_inst_5940_: *mut LeanObject,
    mut v_inst_5941_: *mut LeanObject,
    mut v_inst_5942_: *mut LeanObject,
    mut v_inst_5943_: *mut LeanObject,
    mut v_inst_5944_: *mut LeanObject,
    mut v_inst_5945_: *mut LeanObject,
    mut v_x_5946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    v___x_5949_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__0;
    v___x_5950_ = l_Lean_stringToMessageData(v___x_5949_);
    return v___x_5950_;
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(
    mut v_val_5951_: *mut LeanObject,
    mut v_ex_5952_: *mut LeanObject,
    mut v_toPure_5953_: *mut LeanObject,
    mut v_____do__lift_5954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exPosition_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5960_: u8 = 0;
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exPosition_5955_ = l_Lean_FileMap_toPosition(v_____do__lift_5954_, v_val_5951_);
                v_line_5956_ = lean_ctor_get(v_exPosition_5955_, 0);
                v_column_5957_ = lean_ctor_get(v_exPosition_5955_, 1);
                v_isSharedCheck_5977_ = (!lean_is_exclusive(v_exPosition_5955_)) as u8;
                if v_isSharedCheck_5977_ == 0 {
                    v___x_5959_ = v_exPosition_5955_;
                    v_isShared_5960_ = v_isSharedCheck_5977_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_column_5957_);
                    lean_inc(v_line_5956_);
                    lean_dec(v_exPosition_5955_);
                    v___x_5959_ = lean_box(0);
                    v_isShared_5960_ = v_isSharedCheck_5977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5961_ = l_Nat_reprFast(v_line_5956_);
                v___x_5962_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5962_, 0, v___x_5961_);
                v___x_5963_ = l_Lean_MessageData_ofFormat(v___x_5962_);
                v___x_5964_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___closed__1,
                );
                if v_isShared_5960_ == 0 {
                    lean_ctor_set_tag(v___x_5959_, 7);
                    lean_ctor_set(v___x_5959_, 1, v___x_5964_);
                    lean_ctor_set(v___x_5959_, 0, v___x_5963_);
                    v___x_5966_ = v___x_5959_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5976_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5976_, 0, v___x_5963_);
                    lean_ctor_set(v_reuseFailAlloc_5976_, 1, v___x_5964_);
                    v___x_5966_ = v_reuseFailAlloc_5976_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5967_ = l_Nat_reprFast(v_column_5957_);
                v___x_5968_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5968_, 0, v___x_5967_);
                v___x_5969_ = l_Lean_MessageData_ofFormat(v___x_5968_);
                v___x_5970_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5970_, 0, v___x_5966_);
                lean_ctor_set(v___x_5970_, 1, v___x_5969_);
                v___x_5971_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_mkElabAttribute_spec__0_spec__0___closed__19);
                v___x_5972_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5972_, 0, v___x_5970_);
                lean_ctor_set(v___x_5972_, 1, v___x_5971_);
                v___x_5973_ = l_Lean_Exception_toMessageData(v_ex_5952_);
                v___x_5974_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5974_, 0, v___x_5972_);
                lean_ctor_set(v___x_5974_, 1, v___x_5973_);
                v___x_5975_ = lean_apply_2(v_toPure_5953_, lean_box(0), v___x_5974_);
                return v___x_5975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed(
    mut v_val_5978_: *mut LeanObject,
    mut v_ex_5979_: *mut LeanObject,
    mut v_toPure_5980_: *mut LeanObject,
    mut v_____do__lift_5981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5982_: *mut LeanObject = core::ptr::null_mut();
    v_res_5982_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0(
        v_val_5978_,
        v_ex_5979_,
        v_toPure_5980_,
        v_____do__lift_5981_,
    );
    lean_dec(v_val_5978_);
    return v_res_5982_;
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(
    mut v_ex_5983_: *mut LeanObject,
    mut v_toPure_5984_: *mut LeanObject,
    mut v_inst_5985_: *mut LeanObject,
    mut v_toBind_5986_: *mut LeanObject,
    mut v_pos_5987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: u8 = 0;
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    v___x_5988_ = l_Lean_Exception_getRef(v_ex_5983_);
    v___x_5989_ = 0;
    v___x_5990_ = l_Lean_Syntax_getPos_x3f(v___x_5988_, v___x_5989_);
    lean_dec(v___x_5988_);
    if lean_obj_tag(v___x_5990_) == 0 {
        let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_5986_);
        lean_dec_ref(v_inst_5985_);
        v___x_5991_ = l_Lean_Exception_toMessageData(v_ex_5983_);
        v___x_5992_ = lean_apply_2(v_toPure_5984_, lean_box(0), v___x_5991_);
        return v___x_5992_;
    } else {
        let mut v_val_5993_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5994_: u8 = 0;
        v_val_5993_ = lean_ctor_get(v___x_5990_, 0);
        lean_inc(v_val_5993_);
        lean_dec_ref_known(v___x_5990_, 1);
        v___x_5994_ = lean_nat_dec_eq(v_pos_5987_, v_val_5993_);
        if v___x_5994_ == 0 {
            let mut v_toMonadFileMap_5995_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_5996_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
            v_toMonadFileMap_5995_ = lean_ctor_get(v_inst_5985_, 0);
            lean_inc(v_toMonadFileMap_5995_);
            lean_dec_ref(v_inst_5985_);
            v___f_5996_ = lean_alloc_closure(
                l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_5996_, 0, v_val_5993_);
            lean_closure_set(v___f_5996_, 1, v_ex_5983_);
            lean_closure_set(v___f_5996_, 2, v_toPure_5984_);
            v___x_5997_ = lean_apply_4(
                v_toBind_5986_,
                lean_box(0),
                lean_box(0),
                v_toMonadFileMap_5995_,
                v___f_5996_,
            );
            return v___x_5997_;
        } else {
            let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_5993_);
            lean_dec(v_toBind_5986_);
            lean_dec_ref(v_inst_5985_);
            v___x_5998_ = l_Lean_Exception_toMessageData(v_ex_5983_);
            v___x_5999_ = lean_apply_2(v_toPure_5984_, lean_box(0), v___x_5998_);
            return v___x_5999_;
        }
    }
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed(
    mut v_ex_6000_: *mut LeanObject,
    mut v_toPure_6001_: *mut LeanObject,
    mut v_inst_6002_: *mut LeanObject,
    mut v_toBind_6003_: *mut LeanObject,
    mut v_pos_6004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6005_: *mut LeanObject = core::ptr::null_mut();
    v_res_6005_ = l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1(
        v_ex_6000_,
        v_toPure_6001_,
        v_inst_6002_,
        v_toBind_6003_,
        v_pos_6004_,
    );
    lean_dec(v_pos_6004_);
    return v_res_6005_;
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData___redArg(
    mut v_inst_6006_: *mut LeanObject,
    mut v_inst_6007_: *mut LeanObject,
    mut v_ex_6008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6009_ = lean_ctor_get(v_inst_6006_, 0);
    v_toBind_6010_ = lean_ctor_get(v_inst_6006_, 1);
    lean_inc_n(v_toBind_6010_, 2);
    v_toPure_6011_ = lean_ctor_get(v_toApplicative_6009_, 1);
    lean_inc(v_toPure_6011_);
    lean_inc_ref(v_inst_6007_);
    v___x_6012_ = l_Lean_getRefPos___redArg(v_inst_6006_, v_inst_6007_);
    v___f_6013_ = lean_alloc_closure(
        l_Lean_Elab_nestedExceptionToMessageData___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_6013_, 0, v_ex_6008_);
    lean_closure_set(v___f_6013_, 1, v_toPure_6011_);
    lean_closure_set(v___f_6013_, 2, v_inst_6007_);
    lean_closure_set(v___f_6013_, 3, v_toBind_6010_);
    v___x_6014_ = lean_apply_4(
        v_toBind_6010_,
        lean_box(0),
        lean_box(0),
        v___x_6012_,
        v___f_6013_,
    );
    return v___x_6014_;
}
pub unsafe fn l_Lean_Elab_nestedExceptionToMessageData(
    mut v_m_6015_: *mut LeanObject,
    mut v_inst_6016_: *mut LeanObject,
    mut v_inst_6017_: *mut LeanObject,
    mut v_ex_6018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    v___x_6019_ =
        l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_6016_, v_inst_6017_, v_ex_6018_);
    return v___x_6019_;
}
pub unsafe fn l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0(
    mut v_inst_6020_: *mut LeanObject,
    mut v_inst_6021_: *mut LeanObject,
    mut v_x_6022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    v___x_6023_ =
        l_Lean_Elab_nestedExceptionToMessageData___redArg(v_inst_6020_, v_inst_6021_, v_x_6022_);
    return v___x_6023_;
}
pub unsafe fn _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    v___x_6025_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__0;
    v___x_6026_ = l_Lean_stringToMessageData(v___x_6025_);
    return v___x_6026_;
}
pub unsafe fn l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1(
    mut v_msg_6027_: *mut LeanObject,
    mut v_inst_6028_: *mut LeanObject,
    mut v_inst_6029_: *mut LeanObject,
    mut v_____do__lift_6030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    v___x_6031_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1___closed__1,
    );
    v___x_6032_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_6032_, 0, v_msg_6027_);
    lean_ctor_set(v___x_6032_, 1, v___x_6031_);
    v___x_6033_ = l_Lean_toMessageList(v_____do__lift_6030_);
    v___x_6034_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_6034_, 0, v___x_6032_);
    lean_ctor_set(v___x_6034_, 1, v___x_6033_);
    v___x_6035_ = l_Lean_throwError___redArg(v_inst_6028_, v_inst_6029_, v___x_6034_);
    return v___x_6035_;
}
pub unsafe fn l_Lean_Elab_throwErrorWithNestedErrors___redArg(
    mut v_inst_6036_: *mut LeanObject,
    mut v_inst_6037_: *mut LeanObject,
    mut v_inst_6038_: *mut LeanObject,
    mut v_msg_6039_: *mut LeanObject,
    mut v_exs_6040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6044_: usize = 0;
    let mut v___x_6045_: usize = 0;
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_6041_ = lean_ctor_get(v_inst_6037_, 1);
    lean_inc(v_toBind_6041_);
    lean_inc_ref_n(v_inst_6037_, 2);
    v___f_6042_ = lean_alloc_closure(
        l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6042_, 0, v_inst_6037_);
    lean_closure_set(v___f_6042_, 1, v_inst_6038_);
    v___f_6043_ = lean_alloc_closure(
        l_Lean_Elab_throwErrorWithNestedErrors___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6043_, 0, v_msg_6039_);
    lean_closure_set(v___f_6043_, 1, v_inst_6037_);
    lean_closure_set(v___f_6043_, 2, v_inst_6036_);
    v_sz_6044_ = lean_array_size(v_exs_6040_);
    v___x_6045_ = 0usize;
    v___x_6046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_6037_,
        v___f_6042_,
        v_sz_6044_,
        v___x_6045_,
        v_exs_6040_,
    );
    v___x_6047_ = lean_apply_4(
        v_toBind_6041_,
        lean_box(0),
        lean_box(0),
        v___x_6046_,
        v___f_6043_,
    );
    return v___x_6047_;
}
pub unsafe fn l_Lean_Elab_throwErrorWithNestedErrors(
    mut v_m_6048_: *mut LeanObject,
    mut v_00_u03b1_6049_: *mut LeanObject,
    mut v_inst_6050_: *mut LeanObject,
    mut v_inst_6051_: *mut LeanObject,
    mut v_inst_6052_: *mut LeanObject,
    mut v_msg_6053_: *mut LeanObject,
    mut v_exs_6054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: u8 = 0;
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    v___x_6122_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_;
    v___x_6123_ = 0;
    v___x_6124_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_;
    v___x_6125_ = l_Lean_registerTraceClass(v___x_6122_, v___x_6123_, v___x_6124_);
    if lean_obj_tag(v___x_6125_) == 0 {
        let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_6125_, 1);
        v___x_6126_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_;
        v___x_6127_ = l_Lean_registerTraceClass(v___x_6126_, v___x_6123_, v___x_6124_);
        if lean_obj_tag(v___x_6127_) == 0 {
            let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6129_: u8 = 0;
            let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_6127_, 1);
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
    mut v_a_6131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6132_: *mut LeanObject = core::ptr::null_mut();
    v_res_6132_ = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
    return v_res_6132_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_KeyedDeclsAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_BuiltinDocAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1710170986____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_pp_macroStack = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_pp_macroStack);
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_1238572749____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_macroAttribute = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_macroAttribute);
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_macroAttribute___regBuiltin_Lean_Elab_macroAttribute_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Util_0__Lean_Elab_initFn_00___x40_Lean_Elab_Util_2034298159____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_mkElabAttribute___auto__1 = _init_l_Lean_Elab_mkElabAttribute___auto__1();
    lean_mark_persistent(l_Lean_Elab_mkElabAttribute___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Extension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_KeyedDeclsAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_BuiltinDocAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Util(builtin);
}
