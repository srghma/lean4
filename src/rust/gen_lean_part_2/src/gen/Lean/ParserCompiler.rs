// Lean compiler output
// Module: Lean.ParserCompiler
// Imports: Lean.Meta.ReduceEval Lean.Meta.WHNF Lean.KeyedDeclsAttribute Lean.ParserCompiler.Attribute Lean.Parser.Extension Init.Data.Range.Polymorphic.Iterators
use crate::ffi::{
    lean_array_fget, lean_array_get, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_uget_borrowed, lean_has_compile_error, lean_infer_type, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_replace_expr, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_zipIdx___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Meta::Defs::lean_mk_syntax_ident;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_replaceRef};
use crate::r#gen::Lean::AddDecl::l_Lean_addAndCompile;
use crate::r#gen::Lean::Attributes::l_Lean_Attribute_add;
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_type, l_Lean_ConstantInfo_value_x3f, l_Lean_ConstantInfo_value_x21,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortCommandExceptionId;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_evalConstCheck___redArg,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConst,
    l_Lean_Expr_isConstOf, l_Lean_Expr_isOptParam, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkConst, l_Lean_mkForall,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::{
    initialize_Lean_KeyedDeclsAttribute, runtime_initialize_Lean_KeyedDeclsAttribute,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalContext_getFVar_x21, l_Lean_LocalDecl_type};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::ReduceEval::{
    initialize_Lean_Meta_ReduceEval, l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName,
    runtime_initialize_Lean_Meta_ReduceEval,
};
use crate::r#gen::Lean::Meta::TransparencyMode::l_Lean_Meta_TransparencyMode_lt;
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_unfoldDefinition_x3f, l_Lean_Meta_whnfCore,
    runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::Parser::Extension::{
    initialize_Lean_Parser_Extension, l_Lean_Parser_registerParserAttributeHook,
    runtime_initialize_Lean_Parser_Extension,
};
use crate::r#gen::Lean::ParserCompiler::Attribute::{
    initialize_Lean_ParserCompiler_Attribute,
    l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f,
    l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor,
    runtime_initialize_Lean_ParserCompiler_Attribute,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
pub static l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value:
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
static mut l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value:
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
static mut l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value_aux_0:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value_aux_1:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        1775661699143345266 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0_value:
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
static mut l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0_value:
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
    m_data: [110, 111, 100, 101, 0],
};
static mut l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_0:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        10136201327411625388 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2_value:
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
    m_data: [119, 105, 116, 104, 65, 110, 116, 105, 113, 117, 111, 116, 0],
};
static mut l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_0:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        9171102469834364930 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4_value:
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
    m_data: [108, 101, 97, 100, 105, 110, 103, 78, 111, 100, 101, 0],
};
static mut l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_0:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__4_value)
            as *mut leanh::LeanObject,
        2229813605087390178 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6_value:
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
    m_data: [116, 114, 97, 105, 108, 105, 110, 103, 78, 111, 100, 101, 0],
};
static mut l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_0:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__6_value)
            as *mut leanh::LeanObject,
        7731126556453791499 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,13286986945483979944 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__1_value:
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
    m_data: [115, 105, 109, 112, 108, 101, 0],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__0_value:
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
    m_data: [65, 116, 116, 114, 0],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_0:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_1:
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
            l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_2:
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
            l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        4584992172905639687 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value:
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
            l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        3878072352281346923 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__3_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        100, 111, 110, 39, 116, 32, 107, 110, 111, 119, 32, 104, 111, 119, 32, 116, 111, 32, 103,
        101, 110, 101, 114, 97, 116, 101, 32, 0,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11_value:
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
        32, 102, 111, 114, 32, 110, 111, 110, 45, 112, 97, 114, 115, 101, 114, 32, 99, 111, 109,
        98, 105, 110, 97, 116, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13_value:
    leanh::LeanStringObject<60> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        114, 101, 102, 117, 115, 105, 110, 103, 32, 116, 111, 32, 103, 101, 110, 101, 114, 97, 116,
        101, 32, 99, 111, 100, 101, 32, 102, 111, 114, 32, 105, 109, 112, 111, 114, 116, 101, 100,
        32, 112, 97, 114, 115, 101, 114, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        32, 96, 0,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15_value:
    leanh::LeanStringObject<66> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 66,
    m_capacity: 66,
    m_length: 65,
    m_data: [
        96, 59, 32, 117, 115, 101, 32, 96, 64, 91, 114, 117, 110, 95, 112, 97, 114, 115, 101, 114,
        95, 97, 116, 116, 114, 105, 98, 117, 116, 101, 95, 104, 111, 111, 107, 115, 93, 96, 32,
        111, 110, 32, 105, 116, 115, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 105,
        110, 115, 116, 101, 97, 100, 46, 0,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        32, 102, 111, 114, 32, 110, 111, 110, 45, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
        32, 96, 0,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value:
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
        84, 114, 97, 105, 108, 105, 110, 103, 80, 97, 114, 115, 101, 114, 0,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value_aux_0:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value_aux_1:
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
            l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value:
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
            l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__19_value)
            as *mut leanh::LeanObject,
        8425685303889201640 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        99, 97, 108, 108, 32, 111, 102, 32, 117, 110, 107, 110, 111, 119, 110, 32, 112, 97, 114,
        115, 101, 114, 32, 97, 116, 32, 96, 0,
    ],
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3_value:
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
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value:
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
        84, 114, 97, 105, 108, 105, 110, 103, 80, 97, 114, 115, 101, 114, 68, 101, 115, 99, 114, 0,
    ],
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value
) as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value_aux_0:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value:
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
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__8_value
        ) as *mut leanh::LeanObject,
        18049428212802854473 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 68, 101, 115, 99, 114, 0],
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10_value
) as *mut leanh::LeanObject;
static l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value_aux_0:
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
            l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value:
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
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__10_value
        ) as *mut leanh::LeanObject,
        8878632049041653596 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_ParserCompiler_Context_tyName___redArg(
    mut v_ctx_2366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_categoryAttr_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defn_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_valueTypeName_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_categoryAttr_2367_ = leanh::lean_ctor_get(v_ctx_2366_, 1);
    v_defn_2368_ = leanh::lean_ctor_get(v_categoryAttr_2367_, 0);
    v_valueTypeName_2369_ = leanh::lean_ctor_get(v_defn_2368_, 3);
    leanh::lean_inc(v_valueTypeName_2369_);
    return v_valueTypeName_2369_;
}
pub unsafe fn l_Lean_ParserCompiler_Context_tyName___redArg___boxed(
    mut v_ctx_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2371_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_2370_);
    leanh::lean_dec_ref(v_ctx_2370_);
    return v_res_2371_;
}
pub unsafe fn l_Lean_ParserCompiler_Context_tyName(
    mut v_00_u03b1_2372_: *mut leanh::LeanObject,
    mut v_ctx_2373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2374_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_2373_);
    return v___x_2374_;
}
pub unsafe fn l_Lean_ParserCompiler_Context_tyName___boxed(
    mut v_00_u03b1_2375_: *mut leanh::LeanObject,
    mut v_ctx_2376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2377_ = l_Lean_ParserCompiler_Context_tyName(v_00_u03b1_2375_, v_ctx_2376_);
    leanh::lean_dec_ref(v_ctx_2376_);
    return v_res_2377_;
}
pub unsafe fn l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0(
    mut v_ctx_2383_: *mut leanh::LeanObject,
    mut v_e_2384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2394_ = l_Lean_Expr_isOptParam(v_e_2384_);
                if v___x_2394_ == 0 {
                    v___y_2386_ = v_e_2384_;
                    state = 1;
                    continue;
                } else {
                    v___x_2395_ = l_Lean_Expr_appFn_x21(v_e_2384_);
                    leanh::lean_dec_ref(v_e_2384_);
                    v___x_2396_ = l_Lean_Expr_appArg_x21(v___x_2395_);
                    leanh::lean_dec_ref(v___x_2395_);
                    v___y_2386_ = v___x_2396_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2387_ = l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2;
                v___x_2388_ = l_Lean_Expr_isConstOf(v___y_2386_, v___x_2387_);
                leanh::lean_dec_ref(v___y_2386_);
                if v___x_2388_ == 0 {
                    v___x_2389_ = leanh::lean_box(0);
                    return v___x_2389_;
                } else {
                    v___x_2390_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_2383_);
                    v___x_2391_ = leanh::lean_box(0);
                    v___x_2392_ = l_Lean_mkConst(v___x_2390_, v___x_2391_);
                    v___x_2393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
                    return v___x_2393_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___boxed(
    mut v_ctx_2397_: *mut leanh::LeanObject,
    mut v_e_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0(v_ctx_2397_, v_e_2398_);
    leanh::lean_dec_ref(v_ctx_2397_);
    return v_res_2399_;
}
pub unsafe fn l_Lean_ParserCompiler_replaceParserTy___redArg(
    mut v_ctx_2400_: *mut leanh::LeanObject,
    mut v_e_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2402_ = leanh::lean_alloc_closure(
        l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2402_, 0, v_ctx_2400_);
    v___x_2403_ = lean_replace_expr(v___f_2402_, v_e_2401_);
    leanh::lean_dec_ref(v___f_2402_);
    return v___x_2403_;
}
pub unsafe fn l_Lean_ParserCompiler_replaceParserTy___redArg___boxed(
    mut v_ctx_2404_: *mut leanh::LeanObject,
    mut v_e_2405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2406_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_2404_, v_e_2405_);
    leanh::lean_dec_ref(v_e_2405_);
    return v_res_2406_;
}
pub unsafe fn l_Lean_ParserCompiler_replaceParserTy(
    mut v_00_u03b1_2407_: *mut leanh::LeanObject,
    mut v_ctx_2408_: *mut leanh::LeanObject,
    mut v_e_2409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2410_ = l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_2408_, v_e_2409_);
    return v___x_2410_;
}
pub unsafe fn l_Lean_ParserCompiler_replaceParserTy___boxed(
    mut v_00_u03b1_2411_: *mut leanh::LeanObject,
    mut v_ctx_2412_: *mut leanh::LeanObject,
    mut v_e_2413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2414_ = l_Lean_ParserCompiler_replaceParserTy(v_00_u03b1_2411_, v_ctx_2412_, v_e_2413_);
    leanh::lean_dec_ref(v_e_2413_);
    return v_res_2414_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0(
    mut v_k_2415_: *mut leanh::LeanObject,
    mut v_b_2416_: *mut leanh::LeanObject,
    mut v_c_2417_: *mut leanh::LeanObject,
    mut v___y_2418_: *mut leanh::LeanObject,
    mut v___y_2419_: *mut leanh::LeanObject,
    mut v___y_2420_: *mut leanh::LeanObject,
    mut v___y_2421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2421_);
    leanh::lean_inc_ref(v___y_2420_);
    leanh::lean_inc(v___y_2419_);
    leanh::lean_inc_ref(v___y_2418_);
    v___x_2423_ = leanh::lean_apply_7(
        v_k_2415_,
        v_b_2416_,
        v_c_2417_,
        v___y_2418_,
        v___y_2419_,
        v___y_2420_,
        v___y_2421_,
        leanh::lean_box(0),
    );
    return v___x_2423_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0___boxed(
    mut v_k_2424_: *mut leanh::LeanObject,
    mut v_b_2425_: *mut leanh::LeanObject,
    mut v_c_2426_: *mut leanh::LeanObject,
    mut v___y_2427_: *mut leanh::LeanObject,
    mut v___y_2428_: *mut leanh::LeanObject,
    mut v___y_2429_: *mut leanh::LeanObject,
    mut v___y_2430_: *mut leanh::LeanObject,
    mut v___y_2431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2432_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0(v_k_2424_, v_b_2425_, v_c_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
    leanh::lean_dec(v___y_2430_);
    leanh::lean_dec_ref(v___y_2429_);
    leanh::lean_dec(v___y_2428_);
    leanh::lean_dec_ref(v___y_2427_);
    return v_res_2432_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(
    mut v_e_2433_: *mut leanh::LeanObject,
    mut v_k_2434_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2435_: u8,
    mut v_preserveNondepLet_2436_: u8,
    mut v___y_2437_: *mut leanh::LeanObject,
    mut v___y_2438_: *mut leanh::LeanObject,
    mut v___y_2439_: *mut leanh::LeanObject,
    mut v___y_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2454_: u8 = 0;
    let mut v_a_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2458_: u8 = 0;
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2442_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2442_, 0, v_k_2434_);
                v___x_2443_ = 1;
                v___x_2444_ = 0;
                v___x_2445_ = leanh::lean_box(0);
                v___x_2446_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
                    v_e_2433_,
                    v___x_2443_,
                    v___x_2443_,
                    v_preserveNondepLet_2436_,
                    v___x_2444_,
                    v___x_2445_,
                    v___f_2442_,
                    v_cleanupAnnotations_2435_,
                    v___y_2437_,
                    v___y_2438_,
                    v___y_2439_,
                    v___y_2440_,
                );
                if leanh::lean_obj_tag(v___x_2446_) == 0 {
                    v_a_2447_ = leanh::lean_ctor_get(v___x_2446_, 0);
                    v_isSharedCheck_2454_ = (!leanh::lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2454_ == 0 {
                        v___x_2449_ = v___x_2446_;
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2447_);
                        leanh::lean_dec(v___x_2446_);
                        v___x_2449_ = leanh::lean_box(0);
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2455_ = leanh::lean_ctor_get(v___x_2446_, 0);
                    v_isSharedCheck_2462_ = (!leanh::lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2462_ == 0 {
                        v___x_2457_ = v___x_2446_;
                        v_isShared_2458_ = v_isSharedCheck_2462_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2455_);
                        leanh::lean_dec(v___x_2446_);
                        v___x_2457_ = leanh::lean_box(0);
                        v_isShared_2458_ = v_isSharedCheck_2462_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2450_ == 0 {
                    v___x_2452_ = v___x_2449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
                    v___x_2452_ = v_reuseFailAlloc_2453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2452_;
            }
            3 => {
                if v_isShared_2458_ == 0 {
                    v___x_2460_ = v___x_2457_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
                    v___x_2460_ = v_reuseFailAlloc_2461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___boxed(
    mut v_e_2463_: *mut leanh::LeanObject,
    mut v_k_2464_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2465_: *mut leanh::LeanObject,
    mut v_preserveNondepLet_2466_: *mut leanh::LeanObject,
    mut v___y_2467_: *mut leanh::LeanObject,
    mut v___y_2468_: *mut leanh::LeanObject,
    mut v___y_2469_: *mut leanh::LeanObject,
    mut v___y_2470_: *mut leanh::LeanObject,
    mut v___y_2471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2472_: u8 = 0;
    let mut v_preserveNondepLet_boxed_2473_: u8 = 0;
    let mut v_res_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2472_ = (leanh::lean_unbox(v_cleanupAnnotations_2465_) as u8);
    v_preserveNondepLet_boxed_2473_ = (leanh::lean_unbox(v_preserveNondepLet_2466_) as u8);
    v_res_2474_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_e_2463_, v_k_2464_, v_cleanupAnnotations_boxed_2472_, v_preserveNondepLet_boxed_2473_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
    leanh::lean_dec(v___y_2470_);
    leanh::lean_dec_ref(v___y_2469_);
    leanh::lean_dec(v___y_2468_);
    leanh::lean_dec_ref(v___y_2467_);
    return v_res_2474_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0(
    mut v_00_u03b1_2475_: *mut leanh::LeanObject,
    mut v_e_2476_: *mut leanh::LeanObject,
    mut v_k_2477_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2478_: u8,
    mut v_preserveNondepLet_2479_: u8,
    mut v___y_2480_: *mut leanh::LeanObject,
    mut v___y_2481_: *mut leanh::LeanObject,
    mut v___y_2482_: *mut leanh::LeanObject,
    mut v___y_2483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_e_2476_, v_k_2477_, v_cleanupAnnotations_2478_, v_preserveNondepLet_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
    return v___x_2485_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___boxed(
    mut v_00_u03b1_2486_: *mut leanh::LeanObject,
    mut v_e_2487_: *mut leanh::LeanObject,
    mut v_k_2488_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2489_: *mut leanh::LeanObject,
    mut v_preserveNondepLet_2490_: *mut leanh::LeanObject,
    mut v___y_2491_: *mut leanh::LeanObject,
    mut v___y_2492_: *mut leanh::LeanObject,
    mut v___y_2493_: *mut leanh::LeanObject,
    mut v___y_2494_: *mut leanh::LeanObject,
    mut v___y_2495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2496_: u8 = 0;
    let mut v_preserveNondepLet_boxed_2497_: u8 = 0;
    let mut v_res_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2496_ = (leanh::lean_unbox(v_cleanupAnnotations_2489_) as u8);
    v_preserveNondepLet_boxed_2497_ = (leanh::lean_unbox(v_preserveNondepLet_2490_) as u8);
    v_res_2498_ =
        l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0(
            v_00_u03b1_2486_,
            v_e_2487_,
            v_k_2488_,
            v_cleanupAnnotations_boxed_2496_,
            v_preserveNondepLet_boxed_2497_,
            v___y_2491_,
            v___y_2492_,
            v___y_2493_,
            v___y_2494_,
        );
    leanh::lean_dec(v___y_2494_);
    leanh::lean_dec_ref(v___y_2493_);
    leanh::lean_dec(v___y_2492_);
    leanh::lean_dec_ref(v___y_2491_);
    return v_res_2498_;
}
pub unsafe fn l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(
    mut v_e_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
    mut v_a_2501_: *mut leanh::LeanObject,
    mut v_a_2502_: *mut leanh::LeanObject,
    mut v_a_2503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2506_: u8 = 0;
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2508_: u8 = 0;
    let mut v_ctxApprox_2509_: u8 = 0;
    let mut v_quasiPatternApprox_2510_: u8 = 0;
    let mut v_constApprox_2511_: u8 = 0;
    let mut v_isDefEqStuckEx_2512_: u8 = 0;
    let mut v_unificationHints_2513_: u8 = 0;
    let mut v_proofIrrelevance_2514_: u8 = 0;
    let mut v_assignSyntheticOpaque_2515_: u8 = 0;
    let mut v_offsetCnstrs_2516_: u8 = 0;
    let mut v_etaStruct_2517_: u8 = 0;
    let mut v_univApprox_2518_: u8 = 0;
    let mut v_iota_2519_: u8 = 0;
    let mut v_beta_2520_: u8 = 0;
    let mut v_proj_2521_: u8 = 0;
    let mut v_zeta_2522_: u8 = 0;
    let mut v_zetaDelta_2523_: u8 = 0;
    let mut v_zetaUnused_2524_: u8 = 0;
    let mut v_zetaHave_2525_: u8 = 0;
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2528_: u8 = 0;
    let mut v_trackZetaDelta_2529_: u8 = 0;
    let mut v_zetaDeltaSet_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2536_: u8 = 0;
    let mut v_inTypeClassResolution_2537_: u8 = 0;
    let mut v_cacheInferType_2538_: u8 = 0;
    let mut v_config_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u64 = 0;
    let mut v___x_2542_: u64 = 0;
    let mut v___x_2543_: u64 = 0;
    let mut v___x_2544_: u64 = 0;
    let mut v___x_2545_: u64 = 0;
    let mut v_key_2546_: u64 = 0;
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transparency_2553_: u8 = 0;
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2552_ = l_Lean_Meta_Context_config(v_a_2500_);
                v_transparency_2553_ = leanh::lean_ctor_get_uint8(v___x_2552_, 9 as u32);
                leanh::lean_dec_ref(v___x_2552_);
                v___x_2554_ = 1;
                v___x_2555_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2553_, v___x_2554_);
                if v___x_2555_ == 0 {
                    v___y_2506_ = v_transparency_2553_;
                    state = 1;
                    continue;
                } else {
                    v___y_2506_ = v___x_2554_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2507_ = l_Lean_Meta_Context_config(v_a_2500_);
                v_foApprox_2508_ = leanh::lean_ctor_get_uint8(v___x_2507_, 0 as u32);
                v_ctxApprox_2509_ = leanh::lean_ctor_get_uint8(v___x_2507_, 1 as u32);
                v_quasiPatternApprox_2510_ =
                    leanh::lean_ctor_get_uint8(v___x_2507_, 2 as u32);
                v_constApprox_2511_ = leanh::lean_ctor_get_uint8(v___x_2507_, 3 as u32);
                v_isDefEqStuckEx_2512_ = leanh::lean_ctor_get_uint8(v___x_2507_, 4 as u32);
                v_unificationHints_2513_ = leanh::lean_ctor_get_uint8(v___x_2507_, 5 as u32);
                v_proofIrrelevance_2514_ = leanh::lean_ctor_get_uint8(v___x_2507_, 6 as u32);
                v_assignSyntheticOpaque_2515_ =
                    leanh::lean_ctor_get_uint8(v___x_2507_, 7 as u32);
                v_offsetCnstrs_2516_ = leanh::lean_ctor_get_uint8(v___x_2507_, 8 as u32);
                v_etaStruct_2517_ = leanh::lean_ctor_get_uint8(v___x_2507_, 10 as u32);
                v_univApprox_2518_ = leanh::lean_ctor_get_uint8(v___x_2507_, 11 as u32);
                v_iota_2519_ = leanh::lean_ctor_get_uint8(v___x_2507_, 12 as u32);
                v_beta_2520_ = leanh::lean_ctor_get_uint8(v___x_2507_, 13 as u32);
                v_proj_2521_ = leanh::lean_ctor_get_uint8(v___x_2507_, 14 as u32);
                v_zeta_2522_ = leanh::lean_ctor_get_uint8(v___x_2507_, 15 as u32);
                v_zetaDelta_2523_ = leanh::lean_ctor_get_uint8(v___x_2507_, 16 as u32);
                v_zetaUnused_2524_ = leanh::lean_ctor_get_uint8(v___x_2507_, 17 as u32);
                v_zetaHave_2525_ = leanh::lean_ctor_get_uint8(v___x_2507_, 18 as u32);
                v_isSharedCheck_2551_ = (!leanh::lean_is_exclusive(v___x_2507_)) as u8;
                if v_isSharedCheck_2551_ == 0 {
                    v___x_2527_ = v___x_2507_;
                    v_isShared_2528_ = v_isSharedCheck_2551_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2507_);
                    v___x_2527_ = leanh::lean_box(0);
                    v_isShared_2528_ = v_isSharedCheck_2551_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_2529_ = leanh::lean_ctor_get_uint8(
                    v_a_2500_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2530_ = leanh::lean_ctor_get(v_a_2500_, 1);
                v_lctx_2531_ = leanh::lean_ctor_get(v_a_2500_, 2);
                v_localInstances_2532_ = leanh::lean_ctor_get(v_a_2500_, 3);
                v_defEqCtx_x3f_2533_ = leanh::lean_ctor_get(v_a_2500_, 4);
                v_synthPendingDepth_2534_ = leanh::lean_ctor_get(v_a_2500_, 5);
                v_canUnfold_x3f_2535_ = leanh::lean_ctor_get(v_a_2500_, 6);
                v_univApprox_2536_ = leanh::lean_ctor_get_uint8(
                    v_a_2500_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2537_ = leanh::lean_ctor_get_uint8(
                    v_a_2500_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2538_ = leanh::lean_ctor_get_uint8(
                    v_a_2500_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2528_ == 0 {
                    v_config_2540_ = v___x_2527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2550_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        0 as u32,
                        v_foApprox_2508_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        1 as u32,
                        v_ctxApprox_2509_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        2 as u32,
                        v_quasiPatternApprox_2510_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        3 as u32,
                        v_constApprox_2511_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        4 as u32,
                        v_isDefEqStuckEx_2512_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        5 as u32,
                        v_unificationHints_2513_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        6 as u32,
                        v_proofIrrelevance_2514_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        7 as u32,
                        v_assignSyntheticOpaque_2515_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        8 as u32,
                        v_offsetCnstrs_2516_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        10 as u32,
                        v_etaStruct_2517_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        11 as u32,
                        v_univApprox_2518_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        12 as u32,
                        v_iota_2519_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        13 as u32,
                        v_beta_2520_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        14 as u32,
                        v_proj_2521_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        15 as u32,
                        v_zeta_2522_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        16 as u32,
                        v_zetaDelta_2523_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        17 as u32,
                        v_zetaUnused_2524_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2550_,
                        18 as u32,
                        v_zetaHave_2525_,
                    );
                    v_config_2540_ = v_reuseFailAlloc_2550_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(v_config_2540_, 9 as u32, v___y_2506_);
                v___x_2541_ = l_Lean_Meta_Context_configKey(v_a_2500_);
                v___x_2542_ = 3u64;
                v___x_2543_ = lean_uint64_shift_right(v___x_2541_, v___x_2542_);
                v___x_2544_ = lean_uint64_shift_left(v___x_2543_, v___x_2542_);
                v___x_2545_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2506_);
                v_key_2546_ = lean_uint64_lor(v___x_2544_, v___x_2545_);
                v___x_2547_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2547_, 0, v_config_2540_);
                leanh::lean_ctor_set_uint64(
                    v___x_2547_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2546_,
                );
                leanh::lean_inc(v_canUnfold_x3f_2535_);
                leanh::lean_inc(v_synthPendingDepth_2534_);
                leanh::lean_inc(v_defEqCtx_x3f_2533_);
                leanh::lean_inc_ref(v_localInstances_2532_);
                leanh::lean_inc_ref(v_lctx_2531_);
                leanh::lean_inc(v_zetaDeltaSet_2530_);
                v___x_2548_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2548_, 0, v___x_2547_);
                leanh::lean_ctor_set(v___x_2548_, 1, v_zetaDeltaSet_2530_);
                leanh::lean_ctor_set(v___x_2548_, 2, v_lctx_2531_);
                leanh::lean_ctor_set(v___x_2548_, 3, v_localInstances_2532_);
                leanh::lean_ctor_set(v___x_2548_, 4, v_defEqCtx_x3f_2533_);
                leanh::lean_ctor_set(v___x_2548_, 5, v_synthPendingDepth_2534_);
                leanh::lean_ctor_set(v___x_2548_, 6, v_canUnfold_x3f_2535_);
                leanh::lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2529_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2536_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2537_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2538_,
                );
                v___x_2549_ = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(
                    v_e_2499_,
                    v___x_2548_,
                    v_a_2501_,
                    v_a_2502_,
                    v_a_2503_,
                );
                leanh::lean_dec_ref_known(v___x_2548_, 7);
                return v___x_2549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1___boxed(
    mut v_e_2556_: *mut leanh::LeanObject,
    mut v_a_2557_: *mut leanh::LeanObject,
    mut v_a_2558_: *mut leanh::LeanObject,
    mut v_a_2559_: *mut leanh::LeanObject,
    mut v_a_2560_: *mut leanh::LeanObject,
    mut v_a_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2562_ = l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(
        v_e_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_,
    );
    leanh::lean_dec(v_a_2560_);
    leanh::lean_dec_ref(v_a_2559_);
    leanh::lean_dec(v_a_2558_);
    leanh::lean_dec_ref(v_a_2557_);
    return v_res_2562_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(
    mut v_type_2563_: *mut leanh::LeanObject,
    mut v_k_2564_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2565_: u8,
    mut v___y_2566_: *mut leanh::LeanObject,
    mut v___y_2567_: *mut leanh::LeanObject,
    mut v___y_2568_: *mut leanh::LeanObject,
    mut v___y_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: u8 = 0;
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2578_: u8 = 0;
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut v_a_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2586_: u8 = 0;
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2571_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2571_, 0, v_k_2564_);
                v___x_2572_ = 0;
                v___x_2573_ = leanh::lean_box(0);
                v___x_2574_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        leanh::lean_box(0),
                        v___x_2572_,
                        v___x_2573_,
                        v_type_2563_,
                        v___f_2571_,
                        v_cleanupAnnotations_2565_,
                        v___x_2572_,
                        v___y_2566_,
                        v___y_2567_,
                        v___y_2568_,
                        v___y_2569_,
                    );
                if leanh::lean_obj_tag(v___x_2574_) == 0 {
                    v_a_2575_ = leanh::lean_ctor_get(v___x_2574_, 0);
                    v_isSharedCheck_2582_ = (!leanh::lean_is_exclusive(v___x_2574_)) as u8;
                    if v_isSharedCheck_2582_ == 0 {
                        v___x_2577_ = v___x_2574_;
                        v_isShared_2578_ = v_isSharedCheck_2582_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2575_);
                        leanh::lean_dec(v___x_2574_);
                        v___x_2577_ = leanh::lean_box(0);
                        v_isShared_2578_ = v_isSharedCheck_2582_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2583_ = leanh::lean_ctor_get(v___x_2574_, 0);
                    v_isSharedCheck_2590_ = (!leanh::lean_is_exclusive(v___x_2574_)) as u8;
                    if v_isSharedCheck_2590_ == 0 {
                        v___x_2585_ = v___x_2574_;
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2583_);
                        leanh::lean_dec(v___x_2574_);
                        v___x_2585_ = leanh::lean_box(0);
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2578_ == 0 {
                    v___x_2580_ = v___x_2577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
                    v___x_2580_ = v_reuseFailAlloc_2581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2580_;
            }
            3 => {
                if v_isShared_2586_ == 0 {
                    v___x_2588_ = v___x_2585_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2589_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
                    v___x_2588_ = v_reuseFailAlloc_2589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg___boxed(
    mut v_type_2591_: *mut leanh::LeanObject,
    mut v_k_2592_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2593_: *mut leanh::LeanObject,
    mut v___y_2594_: *mut leanh::LeanObject,
    mut v___y_2595_: *mut leanh::LeanObject,
    mut v___y_2596_: *mut leanh::LeanObject,
    mut v___y_2597_: *mut leanh::LeanObject,
    mut v___y_2598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2599_: u8 = 0;
    let mut v_res_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2599_ = (leanh::lean_unbox(v_cleanupAnnotations_2593_) as u8);
    v_res_2600_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_type_2591_, v_k_2592_, v_cleanupAnnotations_boxed_2599_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
    leanh::lean_dec(v___y_2597_);
    leanh::lean_dec_ref(v___y_2596_);
    leanh::lean_dec(v___y_2595_);
    leanh::lean_dec_ref(v___y_2594_);
    return v_res_2600_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3(
    mut v_00_u03b1_2601_: *mut leanh::LeanObject,
    mut v_type_2602_: *mut leanh::LeanObject,
    mut v_k_2603_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2604_: u8,
    mut v___y_2605_: *mut leanh::LeanObject,
    mut v___y_2606_: *mut leanh::LeanObject,
    mut v___y_2607_: *mut leanh::LeanObject,
    mut v___y_2608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2610_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_type_2602_, v_k_2603_, v_cleanupAnnotations_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
    return v___x_2610_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___boxed(
    mut v_00_u03b1_2611_: *mut leanh::LeanObject,
    mut v_type_2612_: *mut leanh::LeanObject,
    mut v_k_2613_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2614_: *mut leanh::LeanObject,
    mut v___y_2615_: *mut leanh::LeanObject,
    mut v___y_2616_: *mut leanh::LeanObject,
    mut v___y_2617_: *mut leanh::LeanObject,
    mut v___y_2618_: *mut leanh::LeanObject,
    mut v___y_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2620_: u8 = 0;
    let mut v_res_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2620_ = (leanh::lean_unbox(v_cleanupAnnotations_2614_) as u8);
    v_res_2621_ =
        l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3(
            v_00_u03b1_2611_,
            v_type_2612_,
            v_k_2613_,
            v_cleanupAnnotations_boxed_2620_,
            v___y_2615_,
            v___y_2616_,
            v___y_2617_,
            v___y_2618_,
        );
    leanh::lean_dec(v___y_2618_);
    leanh::lean_dec_ref(v___y_2617_);
    leanh::lean_dec(v___y_2616_);
    leanh::lean_dec_ref(v___y_2615_);
    return v_res_2621_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(
    mut v___x_2622_: *mut leanh::LeanObject,
    mut v_as_2623_: *mut leanh::LeanObject,
    mut v_i_2624_: usize,
    mut v_stop_2625_: usize,
    mut v_b_2626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: usize = 0;
    let mut v___x_2630_: usize = 0;
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2632_ = lean_usize_dec_eq(v_i_2624_, v_stop_2625_);
                if v___x_2632_ == 0 {
                    v___x_2633_ = lean_array_uget_borrowed(v_as_2623_, v_i_2624_);
                    v_fst_2634_ = leanh::lean_ctor_get(v___x_2633_, 0);
                    leanh::lean_inc_ref(v___x_2622_);
                    v___x_2635_ = l_Lean_LocalContext_getFVar_x21(v___x_2622_, v_fst_2634_);
                    v___x_2636_ = l_Lean_LocalDecl_type(v___x_2635_);
                    leanh::lean_dec_ref(v___x_2635_);
                    v___x_2637_ =
                        l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2;
                    v___x_2638_ = l_Lean_Expr_isConstOf(v___x_2636_, v___x_2637_);
                    leanh::lean_dec_ref(v___x_2636_);
                    if v___x_2638_ == 0 {
                        v___y_2628_ = v_b_2626_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_2633_);
                        v___x_2639_ = lean_array_push(v_b_2626_, v___x_2633_);
                        v___y_2628_ = v___x_2639_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2622_);
                    return v_b_2626_;
                }
            }
            1 => {
                v___x_2629_ = 1usize;
                v___x_2630_ = lean_usize_add(v_i_2624_, v___x_2629_);
                v_i_2624_ = v___x_2630_;
                v_b_2626_ = v___y_2628_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2___boxed(
    mut v___x_2640_: *mut leanh::LeanObject,
    mut v_as_2641_: *mut leanh::LeanObject,
    mut v_i_2642_: *mut leanh::LeanObject,
    mut v_stop_2643_: *mut leanh::LeanObject,
    mut v_b_2644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2645_: usize = 0;
    let mut v_stop_boxed_2646_: usize = 0;
    let mut v_res_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2645_ = leanh::lean_unbox_usize(v_i_2642_);
    leanh::lean_dec(v_i_2642_);
    v_stop_boxed_2646_ = leanh::lean_unbox_usize(v_stop_2643_);
    leanh::lean_dec(v_stop_2643_);
    v_res_2647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v___x_2640_, v_as_2641_, v_i_boxed_2645_, v_stop_boxed_2646_, v_b_2644_);
    leanh::lean_dec_ref(v_as_2641_);
    return v_res_2647_;
}
pub unsafe fn l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed(
    mut v_x_2648_: *mut leanh::LeanObject,
    mut v_e_2649_: *mut leanh::LeanObject,
    mut v___y_2650_: *mut leanh::LeanObject,
    mut v___y_2651_: *mut leanh::LeanObject,
    mut v___y_2652_: *mut leanh::LeanObject,
    mut v___y_2653_: *mut leanh::LeanObject,
    mut v___y_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(
        v_x_2648_,
        v_e_2649_,
        v___y_2650_,
        v___y_2651_,
        v___y_2652_,
        v___y_2653_,
    );
    leanh::lean_dec(v___y_2653_);
    leanh::lean_dec_ref(v___y_2652_);
    leanh::lean_dec(v___y_2651_);
    leanh::lean_dec_ref(v___y_2650_);
    leanh::lean_dec_ref(v_x_2648_);
    return v_res_2655_;
}
pub unsafe fn l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(
    mut v_a_2658_: *mut leanh::LeanObject,
    mut v_params_2659_: *mut leanh::LeanObject,
    mut v_x_2660_: *mut leanh::LeanObject,
    mut v___y_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
    mut v___y_2663_: *mut leanh::LeanObject,
    mut v___y_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: u8 = 0;
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: u8 = 0;
    let mut v_lctx_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: u8 = 0;
    let mut v___x_2687_: usize = 0;
    let mut v___x_2688_: usize = 0;
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: usize = 0;
    let mut v___x_2691_: usize = 0;
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2666_ = leanh::lean_unsigned_to_nat(0);
                v___x_2681_ = l_Array_zipIdx___redArg(v_params_2659_, v___x_2666_);
                v___x_2682_ = lean_array_get_size(v___x_2681_);
                v___x_2683_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___closed__0;
                v___x_2684_ = lean_nat_dec_lt(v___x_2666_, v___x_2682_);
                if v___x_2684_ == 0 {
                    leanh::lean_dec_ref(v___x_2681_);
                    v___y_2668_ = v___x_2683_;
                    state = 1;
                    continue;
                } else {
                    v_lctx_2685_ = leanh::lean_ctor_get(v___y_2661_, 2);
                    v___x_2686_ = lean_nat_dec_le(v___x_2682_, v___x_2682_);
                    if v___x_2686_ == 0 {
                        if v___x_2684_ == 0 {
                            leanh::lean_dec_ref(v___x_2681_);
                            v___y_2668_ = v___x_2683_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2687_ = 0usize;
                            v___x_2688_ = lean_usize_of_nat(v___x_2682_);
                            leanh::lean_inc_ref(v_lctx_2685_);
                            v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v_lctx_2685_, v___x_2681_, v___x_2687_, v___x_2688_, v___x_2683_);
                            leanh::lean_dec_ref(v___x_2681_);
                            v___y_2668_ = v___x_2689_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2690_ = 0usize;
                        v___x_2691_ = lean_usize_of_nat(v___x_2682_);
                        leanh::lean_inc_ref(v_lctx_2685_);
                        v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__2(v_lctx_2685_, v___x_2681_, v___x_2690_, v___x_2691_, v___x_2683_);
                        leanh::lean_dec_ref(v___x_2681_);
                        v___y_2668_ = v___x_2692_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2669_ = lean_array_get_size(v___y_2668_);
                v___x_2670_ = leanh::lean_unsigned_to_nat(1);
                v___x_2671_ = lean_nat_dec_eq(v___x_2669_, v___x_2670_);
                if v___x_2671_ == 0 {
                    leanh::lean_dec_ref(v___y_2668_);
                    v___x_2672_ = leanh::lean_box(0);
                    v___x_2673_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2673_, 0, v___x_2672_);
                    return v___x_2673_;
                } else {
                    v___x_2674_ = lean_array_fget(v___y_2668_, v___x_2666_);
                    leanh::lean_dec_ref(v___y_2668_);
                    v_snd_2675_ = leanh::lean_ctor_get(v___x_2674_, 1);
                    leanh::lean_inc(v_snd_2675_);
                    leanh::lean_dec(v___x_2674_);
                    v___x_2676_ = l_Lean_Expr_getAppNumArgs(v_a_2658_);
                    v___x_2677_ = lean_nat_sub(v___x_2676_, v_snd_2675_);
                    leanh::lean_dec(v_snd_2675_);
                    leanh::lean_dec(v___x_2676_);
                    v___x_2678_ = lean_nat_sub(v___x_2677_, v___x_2670_);
                    leanh::lean_dec(v___x_2677_);
                    v___x_2679_ = l_Lean_Expr_getRevArg_x21(v_a_2658_, v___x_2678_);
                    v___x_2680_ = l_Lean_ParserCompiler_parserNodeKind_x3f(
                        v___x_2679_,
                        v___y_2661_,
                        v___y_2662_,
                        v___y_2663_,
                        v___y_2664_,
                    );
                    return v___x_2680_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed(
    mut v_a_2693_: *mut leanh::LeanObject,
    mut v_params_2694_: *mut leanh::LeanObject,
    mut v_x_2695_: *mut leanh::LeanObject,
    mut v___y_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
    mut v___y_2698_: *mut leanh::LeanObject,
    mut v___y_2699_: *mut leanh::LeanObject,
    mut v___y_2700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2701_ = l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1(
        v_a_2693_,
        v_params_2694_,
        v_x_2695_,
        v___y_2696_,
        v___y_2697_,
        v___y_2698_,
        v___y_2699_,
    );
    leanh::lean_dec(v___y_2699_);
    leanh::lean_dec_ref(v___y_2698_);
    leanh::lean_dec(v___y_2697_);
    leanh::lean_dec_ref(v___y_2696_);
    leanh::lean_dec_ref(v_x_2695_);
    leanh::lean_dec_ref(v_params_2694_);
    leanh::lean_dec_ref(v_a_2693_);
    return v_res_2701_;
}
pub unsafe fn l_Lean_ParserCompiler_parserNodeKind_x3f(
    mut v_e_2722_: *mut leanh::LeanObject,
    mut v_a_2723_: *mut leanh::LeanObject,
    mut v_a_2724_: *mut leanh::LeanObject,
    mut v_a_2725_: *mut leanh::LeanObject,
    mut v_a_2726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2730_: u8 = 0;
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut v_a_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2753_: u8 = 0;
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: u8 = 0;
    let mut v_reuseFailAlloc_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v___f_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: u8 = 0;
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2766_: u8 = 0;
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: u8 = 0;
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v_a_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2733_ =
                    l_Lean_Meta_whnfCore(v_e_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
                if leanh::lean_obj_tag(v___x_2733_) == 0 {
                    v_a_2734_ = leanh::lean_ctor_get(v___x_2733_, 0);
                    leanh::lean_inc(v_a_2734_);
                    leanh::lean_dec_ref_known(v___x_2733_, 1);
                    v___f_2760_ = leanh::lean_alloc_closure(
                        l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        7,
                        0,
                    );
                    match leanh::lean_obj_tag(v_a_2734_) {
                        6 => {
                            state = 7;
                            continue;
                        }
                        8 => {
                            state = 7;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v___f_2760_);
                            leanh::lean_inc(v_a_2734_);
                            v___f_2764_ = leanh::lean_alloc_closure(
                                l_Lean_ParserCompiler_parserNodeKind_x3f___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                8,
                                1,
                            );
                            leanh::lean_closure_set(v___f_2764_, 0, v_a_2734_);
                            v___x_2790_ = l_Lean_ParserCompiler_parserNodeKind_x3f___closed__5;
                            v___x_2791_ = leanh::lean_unsigned_to_nat(3);
                            v___x_2792_ =
                                l_Lean_Expr_isAppOfArity(v_a_2734_, v___x_2790_, v___x_2791_);
                            if v___x_2792_ == 0 {
                                v___x_2793_ = l_Lean_ParserCompiler_parserNodeKind_x3f___closed__7;
                                v___x_2794_ = leanh::lean_unsigned_to_nat(4);
                                v___x_2795_ =
                                    l_Lean_Expr_isAppOfArity(v_a_2734_, v___x_2793_, v___x_2794_);
                                v___y_2766_ = v___x_2795_;
                                state = 8;
                                continue;
                            } else {
                                v___y_2766_ = v___x_2792_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_2796_ = leanh::lean_ctor_get(v___x_2733_, 0);
                    v_isSharedCheck_2803_ = (!leanh::lean_is_exclusive(v___x_2733_)) as u8;
                    if v_isSharedCheck_2803_ == 0 {
                        v___x_2798_ = v___x_2733_;
                        v_isShared_2799_ = v_isSharedCheck_2803_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2796_);
                        leanh::lean_dec(v___x_2733_);
                        v___x_2798_ = leanh::lean_box(0);
                        v_isShared_2799_ = v_isSharedCheck_2803_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2730_ == 0 {
                    leanh::lean_dec_ref(v___y_2729_);
                    v___x_2731_ = leanh::lean_box(0);
                    v___x_2732_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2732_, 0, v___x_2731_);
                    return v___x_2732_;
                } else {
                    return v___y_2729_;
                }
            }
            2 => {
                v___x_2736_ = l_Lean_Expr_getAppNumArgs(v_a_2734_);
                v___x_2737_ = leanh::lean_unsigned_to_nat(1);
                v___x_2738_ = lean_nat_sub(v___x_2736_, v___x_2737_);
                leanh::lean_dec(v___x_2736_);
                v___x_2739_ = l_Lean_Expr_getRevArg_x21(v_a_2734_, v___x_2738_);
                leanh::lean_dec(v_a_2734_);
                v___x_2740_ =
                    l_Lean_Meta_reduceEval___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__1(
                        v___x_2739_,
                        v_a_2723_,
                        v_a_2724_,
                        v_a_2725_,
                        v_a_2726_,
                    );
                if leanh::lean_obj_tag(v___x_2740_) == 0 {
                    v_a_2741_ = leanh::lean_ctor_get(v___x_2740_, 0);
                    v_isSharedCheck_2749_ = (!leanh::lean_is_exclusive(v___x_2740_)) as u8;
                    if v_isSharedCheck_2749_ == 0 {
                        v___x_2743_ = v___x_2740_;
                        v_isShared_2744_ = v_isSharedCheck_2749_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2741_);
                        leanh::lean_dec(v___x_2740_);
                        v___x_2743_ = leanh::lean_box(0);
                        v_isShared_2744_ = v_isSharedCheck_2749_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2750_ = leanh::lean_ctor_get(v___x_2740_, 0);
                    v_isSharedCheck_2759_ = (!leanh::lean_is_exclusive(v___x_2740_)) as u8;
                    if v_isSharedCheck_2759_ == 0 {
                        v___x_2752_ = v___x_2740_;
                        v_isShared_2753_ = v_isSharedCheck_2759_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2750_);
                        leanh::lean_dec(v___x_2740_);
                        v___x_2752_ = leanh::lean_box(0);
                        v_isShared_2753_ = v_isSharedCheck_2759_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2745_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2745_, 0, v_a_2741_);
                if v_isShared_2744_ == 0 {
                    leanh::lean_ctor_set(v___x_2743_, 0, v___x_2745_);
                    v___x_2747_ = v___x_2743_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
                    v___x_2747_ = v_reuseFailAlloc_2748_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2747_;
            }
            5 => {
                leanh::lean_inc(v_a_2750_);
                if v_isShared_2753_ == 0 {
                    v___x_2755_ = v___x_2752_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2750_);
                    v___x_2755_ = v_reuseFailAlloc_2758_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2756_ = l_Lean_Exception_isInterrupt(v_a_2750_);
                if v___x_2756_ == 0 {
                    v___x_2757_ = l_Lean_Exception_isRuntime(v_a_2750_);
                    v___y_2729_ = v___x_2755_;
                    v___y_2730_ = v___x_2757_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_2750_);
                    v___y_2729_ = v___x_2755_;
                    v___y_2730_ = v___x_2756_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_2762_ = 0;
                v___x_2763_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_a_2734_, v___f_2760_, v___x_2762_, v___x_2762_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
                return v___x_2763_;
            }
            8 => {
                if v___y_2766_ == 0 {
                    v___x_2767_ = l_Lean_ParserCompiler_parserNodeKind_x3f___closed__1;
                    v___x_2768_ = leanh::lean_unsigned_to_nat(2);
                    v___x_2769_ = l_Lean_Expr_isAppOfArity(v_a_2734_, v___x_2767_, v___x_2768_);
                    if v___x_2769_ == 0 {
                        v___x_2770_ = l_Lean_ParserCompiler_parserNodeKind_x3f___closed__3;
                        v___x_2771_ = l_Lean_Expr_isAppOfArity(v_a_2734_, v___x_2770_, v___x_2768_);
                        if v___x_2771_ == 0 {
                            v___x_2772_ = l_Lean_Expr_getAppFn(v_a_2734_);
                            leanh::lean_dec(v_a_2734_);
                            leanh::lean_inc(v_a_2726_);
                            leanh::lean_inc_ref(v_a_2725_);
                            leanh::lean_inc(v_a_2724_);
                            leanh::lean_inc_ref(v_a_2723_);
                            v___x_2773_ = lean_infer_type(
                                v___x_2772_,
                                v_a_2723_,
                                v_a_2724_,
                                v_a_2725_,
                                v_a_2726_,
                            );
                            if leanh::lean_obj_tag(v___x_2773_) == 0 {
                                v_a_2774_ = leanh::lean_ctor_get(v___x_2773_, 0);
                                leanh::lean_inc(v_a_2774_);
                                leanh::lean_dec_ref_known(v___x_2773_, 1);
                                v___x_2775_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_2774_, v___f_2764_, v___x_2771_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
                                return v___x_2775_;
                            } else {
                                leanh::lean_dec_ref(v___f_2764_);
                                v_a_2776_ = leanh::lean_ctor_get(v___x_2773_, 0);
                                v_isSharedCheck_2783_ =
                                    (!leanh::lean_is_exclusive(v___x_2773_)) as u8;
                                if v_isSharedCheck_2783_ == 0 {
                                    v___x_2778_ = v___x_2773_;
                                    v_isShared_2779_ = v_isSharedCheck_2783_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2776_);
                                    leanh::lean_dec(v___x_2773_);
                                    v___x_2778_ = leanh::lean_box(0);
                                    v_isShared_2779_ = v_isSharedCheck_2783_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___f_2764_);
                            v___x_2784_ = leanh::lean_unsigned_to_nat(1);
                            v___x_2785_ = l_Lean_Expr_getAppNumArgs(v_a_2734_);
                            v___x_2786_ = lean_nat_sub(v___x_2785_, v___x_2784_);
                            leanh::lean_dec(v___x_2785_);
                            v___x_2787_ = lean_nat_sub(v___x_2786_, v___x_2784_);
                            leanh::lean_dec(v___x_2786_);
                            v___x_2788_ = l_Lean_Expr_getRevArg_x21(v_a_2734_, v___x_2787_);
                            leanh::lean_dec(v_a_2734_);
                            v_e_2722_ = v___x_2788_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_2764_);
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_2764_);
                    state = 2;
                    continue;
                }
            }
            9 => {
                if v_isShared_2779_ == 0 {
                    v___x_2781_ = v___x_2778_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
                    v___x_2781_ = v_reuseFailAlloc_2782_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2781_;
            }
            11 => {
                if v_isShared_2799_ == 0 {
                    v___x_2801_ = v___x_2798_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2802_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
                    v___x_2801_ = v_reuseFailAlloc_2802_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_parserNodeKind_x3f___lam__0(
    mut v_x_2804_: *mut leanh::LeanObject,
    mut v_e_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
    mut v___y_2808_: *mut leanh::LeanObject,
    mut v___y_2809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2811_ = l_Lean_ParserCompiler_parserNodeKind_x3f(
        v_e_2805_,
        v___y_2806_,
        v___y_2807_,
        v___y_2808_,
        v___y_2809_,
    );
    return v___x_2811_;
}
pub unsafe fn l_Lean_ParserCompiler_parserNodeKind_x3f___boxed(
    mut v_e_2812_: *mut leanh::LeanObject,
    mut v_a_2813_: *mut leanh::LeanObject,
    mut v_a_2814_: *mut leanh::LeanObject,
    mut v_a_2815_: *mut leanh::LeanObject,
    mut v_a_2816_: *mut leanh::LeanObject,
    mut v_a_2817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2818_ = l_Lean_ParserCompiler_parserNodeKind_x3f(
        v_e_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_,
    );
    leanh::lean_dec(v_a_2816_);
    leanh::lean_dec_ref(v_a_2815_);
    leanh::lean_dec(v_a_2814_);
    leanh::lean_dec_ref(v_a_2813_);
    return v_res_2818_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(
    mut v_ctx_2822_: *mut leanh::LeanObject,
    mut v_as_2823_: *mut leanh::LeanObject,
    mut v_i_2824_: usize,
    mut v_stop_2825_: usize,
    mut v_b_2826_: *mut leanh::LeanObject,
    mut v___y_2827_: *mut leanh::LeanObject,
    mut v___y_2828_: *mut leanh::LeanObject,
    mut v___y_2829_: *mut leanh::LeanObject,
    mut v___y_2830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2832_: u8 = 0;
    let mut v___x_2833_: usize = 0;
    let mut v___x_2834_: usize = 0;
    let mut v_a_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: u8 = 0;
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2832_ = lean_usize_dec_eq(v_i_2824_, v_stop_2825_);
                if v___x_2832_ == 0 {
                    v___x_2833_ = 1usize;
                    v___x_2834_ = lean_usize_sub(v_i_2824_, v___x_2833_);
                    v___x_2841_ = lean_array_uget_borrowed(v_as_2823_, v___x_2834_);
                    leanh::lean_inc(v___y_2830_);
                    leanh::lean_inc_ref(v___y_2829_);
                    leanh::lean_inc(v___y_2828_);
                    leanh::lean_inc_ref(v___y_2827_);
                    leanh::lean_inc(v___x_2841_);
                    v___x_2842_ = lean_infer_type(
                        v___x_2841_,
                        v___y_2827_,
                        v___y_2828_,
                        v___y_2829_,
                        v___y_2830_,
                    );
                    if leanh::lean_obj_tag(v___x_2842_) == 0 {
                        v_a_2843_ = leanh::lean_ctor_get(v___x_2842_, 0);
                        leanh::lean_inc(v_a_2843_);
                        leanh::lean_dec_ref_known(v___x_2842_, 1);
                        leanh::lean_inc_ref(v_ctx_2822_);
                        v___x_2844_ =
                            l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_2822_, v_a_2843_);
                        leanh::lean_dec(v_a_2843_);
                        v_a_2836_ = v___x_2844_;
                        state = 1;
                        continue;
                    } else {
                        if leanh::lean_obj_tag(v___x_2842_) == 0 {
                            v_a_2845_ = leanh::lean_ctor_get(v___x_2842_, 0);
                            leanh::lean_inc(v_a_2845_);
                            leanh::lean_dec_ref_known(v___x_2842_, 1);
                            v_a_2836_ = v_a_2845_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_2826_);
                            if leanh::lean_obj_tag(v___x_2842_) == 0 {
                                v_a_2846_ = leanh::lean_ctor_get(v___x_2842_, 0);
                                leanh::lean_inc(v_a_2846_);
                                leanh::lean_dec_ref_known(v___x_2842_, 1);
                                v_i_2824_ = v___x_2834_;
                                v_b_2826_ = v_a_2846_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_ctx_2822_);
                                return v___x_2842_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_ctx_2822_);
                    v___x_2848_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2848_, 0, v_b_2826_);
                    return v___x_2848_;
                }
            }
            1 => {
                v___x_2837_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___closed__1;
                v___x_2838_ = 0;
                v___x_2839_ = l_Lean_mkForall(v___x_2837_, v___x_2838_, v_a_2836_, v_b_2826_);
                v_i_2824_ = v___x_2834_;
                v_b_2826_ = v___x_2839_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg___boxed(
    mut v_ctx_2849_: *mut leanh::LeanObject,
    mut v_as_2850_: *mut leanh::LeanObject,
    mut v_i_2851_: *mut leanh::LeanObject,
    mut v_stop_2852_: *mut leanh::LeanObject,
    mut v_b_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
    mut v___y_2856_: *mut leanh::LeanObject,
    mut v___y_2857_: *mut leanh::LeanObject,
    mut v___y_2858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2859_: usize = 0;
    let mut v_stop_boxed_2860_: usize = 0;
    let mut v_res_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2859_ = leanh::lean_unbox_usize(v_i_2851_);
    leanh::lean_dec(v_i_2851_);
    v_stop_boxed_2860_ = leanh::lean_unbox_usize(v_stop_2852_);
    leanh::lean_dec(v_stop_2852_);
    v_res_2861_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_2849_, v_as_2850_, v_i_boxed_2859_, v_stop_boxed_2860_, v_b_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
    leanh::lean_dec(v___y_2857_);
    leanh::lean_dec_ref(v___y_2856_);
    leanh::lean_dec(v___y_2855_);
    leanh::lean_dec_ref(v___y_2854_);
    leanh::lean_dec_ref(v_as_2850_);
    return v_res_2861_;
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(
    mut v_ctx_2862_: *mut leanh::LeanObject,
    mut v_params_2863_: *mut leanh::LeanObject,
    mut v_x_2864_: *mut leanh::LeanObject,
    mut v___y_2865_: *mut leanh::LeanObject,
    mut v___y_2866_: *mut leanh::LeanObject,
    mut v___y_2867_: *mut leanh::LeanObject,
    mut v___y_2868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: u8 = 0;
    v___x_2870_ = l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_2862_);
    v___x_2871_ = leanh::lean_box(0);
    v___x_2872_ = l_Lean_mkConst(v___x_2870_, v___x_2871_);
    v___x_2873_ = lean_array_get_size(v_params_2863_);
    v___x_2874_ = leanh::lean_unsigned_to_nat(0);
    v___x_2875_ = lean_nat_dec_lt(v___x_2874_, v___x_2873_);
    if v___x_2875_ == 0 {
        let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ctx_2862_);
        v___x_2876_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2876_, 0, v___x_2872_);
        return v___x_2876_;
    } else {
        let mut v___x_2877_: usize = 0;
        let mut v___x_2878_: usize = 0;
        let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2877_ = lean_usize_of_nat(v___x_2873_);
        v___x_2878_ = 0usize;
        v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_2862_, v_params_2863_, v___x_2877_, v___x_2878_, v___x_2872_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
        return v___x_2879_;
    }
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed(
    mut v_ctx_2880_: *mut leanh::LeanObject,
    mut v_params_2881_: *mut leanh::LeanObject,
    mut v_x_2882_: *mut leanh::LeanObject,
    mut v___y_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2888_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3(
        v_ctx_2880_,
        v_params_2881_,
        v_x_2882_,
        v___y_2883_,
        v___y_2884_,
        v___y_2885_,
        v___y_2886_,
    );
    leanh::lean_dec(v___y_2886_);
    leanh::lean_dec_ref(v___y_2885_);
    leanh::lean_dec(v___y_2884_);
    leanh::lean_dec_ref(v___y_2883_);
    leanh::lean_dec_ref(v_x_2882_);
    leanh::lean_dec_ref(v_params_2881_);
    return v_res_2888_;
}
pub unsafe fn l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(
    mut v_k_2889_: *mut leanh::LeanObject,
    mut v_usedLetOnly_2890_: u8,
    mut v_xs_2891_: *mut leanh::LeanObject,
    mut v_b_2892_: *mut leanh::LeanObject,
    mut v___y_2893_: *mut leanh::LeanObject,
    mut v___y_2894_: *mut leanh::LeanObject,
    mut v___y_2895_: *mut leanh::LeanObject,
    mut v___y_2896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2896_);
    leanh::lean_inc_ref(v___y_2895_);
    leanh::lean_inc(v___y_2894_);
    leanh::lean_inc_ref(v___y_2893_);
    leanh::lean_inc_ref(v_xs_2891_);
    v___x_2898_ = leanh::lean_apply_7(
        v_k_2889_,
        v_xs_2891_,
        v_b_2892_,
        v___y_2893_,
        v___y_2894_,
        v___y_2895_,
        v___y_2896_,
        leanh::lean_box(0),
    );
    if leanh::lean_obj_tag(v___x_2898_) == 0 {
        let mut v_a_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: u8 = 0;
        let mut v___x_2901_: u8 = 0;
        let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2899_ = leanh::lean_ctor_get(v___x_2898_, 0);
        leanh::lean_inc(v_a_2899_);
        leanh::lean_dec_ref_known(v___x_2898_, 1);
        v___x_2900_ = 0;
        v___x_2901_ = 1;
        v___x_2902_ = l_Lean_Meta_mkLambdaFVars(
            v_xs_2891_,
            v_a_2899_,
            v___x_2900_,
            v_usedLetOnly_2890_,
            v___x_2900_,
            v___x_2900_,
            v___x_2901_,
            v___y_2893_,
            v___y_2894_,
            v___y_2895_,
            v___y_2896_,
        );
        leanh::lean_dec_ref(v_xs_2891_);
        return v___x_2902_;
    } else {
        leanh::lean_dec_ref(v_xs_2891_);
        return v___x_2898_;
    }
}
pub unsafe fn l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed(
    mut v_k_2903_: *mut leanh::LeanObject,
    mut v_usedLetOnly_2904_: *mut leanh::LeanObject,
    mut v_xs_2905_: *mut leanh::LeanObject,
    mut v_b_2906_: *mut leanh::LeanObject,
    mut v___y_2907_: *mut leanh::LeanObject,
    mut v___y_2908_: *mut leanh::LeanObject,
    mut v___y_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_usedLetOnly_boxed_2912_: u8 = 0;
    let mut v_res_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_2912_ = (leanh::lean_unbox(v_usedLetOnly_2904_) as u8);
    v_res_2913_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0(v_k_2903_, v_usedLetOnly_boxed_2912_, v_xs_2905_, v_b_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
    leanh::lean_dec(v___y_2910_);
    leanh::lean_dec_ref(v___y_2909_);
    leanh::lean_dec(v___y_2908_);
    leanh::lean_dec_ref(v___y_2907_);
    return v_res_2913_;
}
pub unsafe fn l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(
    mut v_e_2914_: *mut leanh::LeanObject,
    mut v_k_2915_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2916_: u8,
    mut v_preserveNondepLet_2917_: u8,
    mut v_usedLetOnly_2918_: u8,
    mut v___y_2919_: *mut leanh::LeanObject,
    mut v___y_2920_: *mut leanh::LeanObject,
    mut v___y_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2924_ = leanh::lean_box((v_usedLetOnly_2918_) as usize);
    v___f_2925_ = leanh::lean_alloc_closure(l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
    leanh::lean_closure_set(v___f_2925_, 0, v_k_2915_);
    leanh::lean_closure_set(v___f_2925_, 1, v___x_2924_);
    v___x_2926_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__0___redArg(v_e_2914_, v___f_2925_, v_cleanupAnnotations_2916_, v_preserveNondepLet_2917_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
    return v___x_2926_;
}
pub unsafe fn l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2___boxed(
    mut v_e_2927_: *mut leanh::LeanObject,
    mut v_k_2928_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2929_: *mut leanh::LeanObject,
    mut v_preserveNondepLet_2930_: *mut leanh::LeanObject,
    mut v_usedLetOnly_2931_: *mut leanh::LeanObject,
    mut v___y_2932_: *mut leanh::LeanObject,
    mut v___y_2933_: *mut leanh::LeanObject,
    mut v___y_2934_: *mut leanh::LeanObject,
    mut v___y_2935_: *mut leanh::LeanObject,
    mut v___y_2936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2937_: u8 = 0;
    let mut v_preserveNondepLet_boxed_2938_: u8 = 0;
    let mut v_usedLetOnly_boxed_2939_: u8 = 0;
    let mut v_res_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2937_ = (leanh::lean_unbox(v_cleanupAnnotations_2929_) as u8);
    v_preserveNondepLet_boxed_2938_ = (leanh::lean_unbox(v_preserveNondepLet_2930_) as u8);
    v_usedLetOnly_boxed_2939_ = (leanh::lean_unbox(v_usedLetOnly_2931_) as u8);
    v_res_2940_ =
        l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(
            v_e_2927_,
            v_k_2928_,
            v_cleanupAnnotations_boxed_2937_,
            v_preserveNondepLet_boxed_2938_,
            v_usedLetOnly_boxed_2939_,
            v___y_2932_,
            v___y_2933_,
            v___y_2934_,
            v___y_2935_,
        );
    leanh::lean_dec(v___y_2935_);
    leanh::lean_dec_ref(v___y_2934_);
    leanh::lean_dec(v___y_2933_);
    leanh::lean_dec_ref(v___y_2932_);
    return v_res_2940_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2941_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2941_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2942_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0);
    v___x_2943_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2943_, 0, v___x_2942_);
    return v___x_2943_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2944_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_2945_ = leanh::lean_unsigned_to_nat(0);
    v___x_2946_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2946_, 0, v___x_2945_);
    leanh::lean_ctor_set(v___x_2946_, 1, v___x_2945_);
    leanh::lean_ctor_set(v___x_2946_, 2, v___x_2945_);
    leanh::lean_ctor_set(v___x_2946_, 3, v___x_2945_);
    leanh::lean_ctor_set(v___x_2946_, 4, v___x_2944_);
    leanh::lean_ctor_set(v___x_2946_, 5, v___x_2944_);
    leanh::lean_ctor_set(v___x_2946_, 6, v___x_2944_);
    leanh::lean_ctor_set(v___x_2946_, 7, v___x_2944_);
    leanh::lean_ctor_set(v___x_2946_, 8, v___x_2944_);
    leanh::lean_ctor_set(v___x_2946_, 9, v___x_2944_);
    return v___x_2946_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = leanh::lean_unsigned_to_nat(32);
    v___x_2948_ = lean_mk_empty_array_with_capacity(v___x_2947_);
    v___x_2949_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2949_, 0, v___x_2948_);
    return v___x_2949_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2950_: usize = 0;
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2950_ = 5usize;
    v___x_2951_ = leanh::lean_unsigned_to_nat(0);
    v___x_2952_ = leanh::lean_unsigned_to_nat(32);
    v___x_2953_ = lean_mk_empty_array_with_capacity(v___x_2952_);
    v___x_2954_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
    v___x_2955_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2955_, 0, v___x_2954_);
    leanh::lean_ctor_set(v___x_2955_, 1, v___x_2953_);
    leanh::lean_ctor_set(v___x_2955_, 2, v___x_2951_);
    leanh::lean_ctor_set(v___x_2955_, 3, v___x_2951_);
    leanh::lean_ctor_set_usize(v___x_2955_, 4, v___x_2950_);
    return v___x_2955_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2956_ = leanh::lean_box(1);
    v___x_2957_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_2958_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_2959_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2959_, 0, v___x_2958_);
    leanh::lean_ctor_set(v___x_2959_, 1, v___x_2957_);
    leanh::lean_ctor_set(v___x_2959_, 2, v___x_2956_);
    return v___x_2959_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2961_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_2962_ = l_Lean_stringToMessageData(v___x_2961_);
    return v___x_2962_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2964_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_2965_ = l_Lean_stringToMessageData(v___x_2964_);
    return v___x_2965_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2967_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_2968_ = l_Lean_stringToMessageData(v___x_2967_);
    return v___x_2968_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2970_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_2971_ = l_Lean_stringToMessageData(v___x_2970_);
    return v___x_2971_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2973_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__14;
    v___x_2974_ = l_Lean_stringToMessageData(v___x_2973_);
    return v___x_2974_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2976_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__16;
    v___x_2977_ = l_Lean_stringToMessageData(v___x_2976_);
    return v___x_2977_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2979_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__18;
    v___x_2980_ = l_Lean_stringToMessageData(v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(
    mut v_msg_2981_: *mut leanh::LeanObject,
    mut v_declHint_2982_: *mut leanh::LeanObject,
    mut v___y_2983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: u8 = 0;
    let mut v_isExporting_2988_: u8 = 0;
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3010_: u8 = 0;
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: u8 = 0;
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2985_ = lean_st_ref_get(v___y_2983_);
                v_env_2986_ = leanh::lean_ctor_get(v___x_2985_, 0);
                leanh::lean_inc_ref(v_env_2986_);
                leanh::lean_dec(v___x_2985_);
                v___x_2987_ = l_Lean_Name_isAnonymous(v_declHint_2982_);
                if v___x_2987_ == 0 {
                    v_isExporting_2988_ = leanh::lean_ctor_get_uint8(
                        v_env_2986_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2988_ == 0 {
                        leanh::lean_dec_ref(v_env_2986_);
                        leanh::lean_dec(v_declHint_2982_);
                        v___x_2989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2989_, 0, v_msg_2981_);
                        return v___x_2989_;
                    } else {
                        leanh::lean_inc_ref(v_env_2986_);
                        v___x_2990_ = l_Lean_Environment_setExporting(v_env_2986_, v___x_2987_);
                        leanh::lean_inc(v_declHint_2982_);
                        leanh::lean_inc_ref(v___x_2990_);
                        v___x_2991_ = l_Lean_Environment_contains(
                            v___x_2990_,
                            v_declHint_2982_,
                            v_isExporting_2988_,
                        );
                        if v___x_2991_ == 0 {
                            leanh::lean_dec_ref(v___x_2990_);
                            leanh::lean_dec_ref(v_env_2986_);
                            leanh::lean_dec(v_declHint_2982_);
                            v___x_2992_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2992_, 0, v_msg_2981_);
                            return v___x_2992_;
                        } else {
                            v___x_2993_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_2994_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
                            v___x_2995_ = l_Lean_Options_empty;
                            v___x_2996_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_2996_, 0, v___x_2990_);
                            leanh::lean_ctor_set(v___x_2996_, 1, v___x_2993_);
                            leanh::lean_ctor_set(v___x_2996_, 2, v___x_2994_);
                            leanh::lean_ctor_set(v___x_2996_, 3, v___x_2995_);
                            leanh::lean_inc(v_declHint_2982_);
                            v___x_2997_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2982_, v___x_2987_);
                            v_c_2998_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_2998_, 0, v___x_2996_);
                            leanh::lean_ctor_set(v_c_2998_, 1, v___x_2997_);
                            v___x_2999_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2986_,
                                v_declHint_2982_,
                            );
                            if leanh::lean_obj_tag(v___x_2999_) == 0 {
                                leanh::lean_dec_ref(v_env_2986_);
                                leanh::lean_dec(v_declHint_2982_);
                                v___x_3000_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_3001_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3001_, 0, v___x_3000_);
                                leanh::lean_ctor_set(v___x_3001_, 1, v_c_2998_);
                                v___x_3002_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
                                v___x_3003_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3003_, 0, v___x_3001_);
                                leanh::lean_ctor_set(v___x_3003_, 1, v___x_3002_);
                                v___x_3004_ = l_Lean_MessageData_note(v___x_3003_);
                                v___x_3005_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3005_, 0, v_msg_2981_);
                                leanh::lean_ctor_set(v___x_3005_, 1, v___x_3004_);
                                v___x_3006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3006_, 0, v___x_3005_);
                                return v___x_3006_;
                            } else {
                                v_val_3007_ = leanh::lean_ctor_get(v___x_2999_, 0);
                                v_isSharedCheck_3042_ =
                                    (!leanh::lean_is_exclusive(v___x_2999_)) as u8;
                                if v_isSharedCheck_3042_ == 0 {
                                    v___x_3009_ = v___x_2999_;
                                    v_isShared_3010_ = v_isSharedCheck_3042_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3007_);
                                    leanh::lean_dec(v___x_2999_);
                                    v___x_3009_ = leanh::lean_box(0);
                                    v_isShared_3010_ = v_isSharedCheck_3042_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2986_);
                    leanh::lean_dec(v_declHint_2982_);
                    v___x_3043_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3043_, 0, v_msg_2981_);
                    return v___x_3043_;
                }
            }
            1 => {
                v___x_3011_ = leanh::lean_box(0);
                v___x_3012_ = l_Lean_Environment_header(v_env_2986_);
                leanh::lean_dec_ref(v_env_2986_);
                v___x_3013_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3012_);
                v_mod_3014_ = lean_array_get(v___x_3011_, v___x_3013_, v_val_3007_);
                leanh::lean_dec(v_val_3007_);
                leanh::lean_dec_ref(v___x_3013_);
                v___x_3015_ = l_Lean_isPrivateName(v_declHint_2982_);
                leanh::lean_dec(v_declHint_2982_);
                if v___x_3015_ == 0 {
                    v___x_3016_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_3017_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3017_, 0, v___x_3016_);
                    leanh::lean_ctor_set(v___x_3017_, 1, v_c_2998_);
                    v___x_3018_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_3019_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3019_, 0, v___x_3017_);
                    leanh::lean_ctor_set(v___x_3019_, 1, v___x_3018_);
                    v___x_3020_ = l_Lean_MessageData_ofName(v_mod_3014_);
                    v___x_3021_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3021_, 0, v___x_3019_);
                    leanh::lean_ctor_set(v___x_3021_, 1, v___x_3020_);
                    v___x_3022_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_3023_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3023_, 0, v___x_3021_);
                    leanh::lean_ctor_set(v___x_3023_, 1, v___x_3022_);
                    v___x_3024_ = l_Lean_MessageData_note(v___x_3023_);
                    v___x_3025_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3025_, 0, v_msg_2981_);
                    leanh::lean_ctor_set(v___x_3025_, 1, v___x_3024_);
                    if v_isShared_3010_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3009_, 0);
                        leanh::lean_ctor_set(v___x_3009_, 0, v___x_3025_);
                        v___x_3027_ = v___x_3009_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3028_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
                        v___x_3027_ = v_reuseFailAlloc_3028_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3029_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_3030_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3030_, 0, v___x_3029_);
                    leanh::lean_ctor_set(v___x_3030_, 1, v_c_2998_);
                    v___x_3031_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_3032_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3032_, 0, v___x_3030_);
                    leanh::lean_ctor_set(v___x_3032_, 1, v___x_3031_);
                    v___x_3033_ = l_Lean_MessageData_ofName(v_mod_3014_);
                    v___x_3034_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3034_, 0, v___x_3032_);
                    leanh::lean_ctor_set(v___x_3034_, 1, v___x_3033_);
                    v___x_3035_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
                    v___x_3036_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3036_, 0, v___x_3034_);
                    leanh::lean_ctor_set(v___x_3036_, 1, v___x_3035_);
                    v___x_3037_ = l_Lean_MessageData_note(v___x_3036_);
                    v___x_3038_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3038_, 0, v_msg_2981_);
                    leanh::lean_ctor_set(v___x_3038_, 1, v___x_3037_);
                    if v_isShared_3010_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3009_, 0);
                        leanh::lean_ctor_set(v___x_3009_, 0, v___x_3038_);
                        v___x_3040_ = v___x_3009_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3041_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
                        v___x_3040_ = v_reuseFailAlloc_3041_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3027_;
            }
            3 => {
                return v___x_3040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_3044_: *mut leanh::LeanObject,
    mut v_declHint_3045_: *mut leanh::LeanObject,
    mut v___y_3046_: *mut leanh::LeanObject,
    mut v___y_3047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3048_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3044_, v_declHint_3045_, v___y_3046_);
    leanh::lean_dec(v___y_3046_);
    return v_res_3048_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(
    mut v_msg_3049_: *mut leanh::LeanObject,
    mut v_declHint_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
    mut v___y_3052_: *mut leanh::LeanObject,
    mut v___y_3053_: *mut leanh::LeanObject,
    mut v___y_3054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3056_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3049_, v_declHint_3050_, v___y_3054_);
                v_a_3057_ = leanh::lean_ctor_get(v___x_3056_, 0);
                v_isSharedCheck_3066_ = (!leanh::lean_is_exclusive(v___x_3056_)) as u8;
                if v_isSharedCheck_3066_ == 0 {
                    v___x_3059_ = v___x_3056_;
                    v_isShared_3060_ = v_isSharedCheck_3066_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3057_);
                    leanh::lean_dec(v___x_3056_);
                    v___x_3059_ = leanh::lean_box(0);
                    v_isShared_3060_ = v_isSharedCheck_3066_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3061_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3062_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3062_, 0, v___x_3061_);
                leanh::lean_ctor_set(v___x_3062_, 1, v_a_3057_);
                if v_isShared_3060_ == 0 {
                    leanh::lean_ctor_set(v___x_3059_, 0, v___x_3062_);
                    v___x_3064_ = v___x_3059_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3065_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3062_);
                    v___x_3064_ = v_reuseFailAlloc_3065_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(
    mut v_msg_3067_: *mut leanh::LeanObject,
    mut v_declHint_3068_: *mut leanh::LeanObject,
    mut v___y_3069_: *mut leanh::LeanObject,
    mut v___y_3070_: *mut leanh::LeanObject,
    mut v___y_3071_: *mut leanh::LeanObject,
    mut v___y_3072_: *mut leanh::LeanObject,
    mut v___y_3073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3074_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_3067_, v_declHint_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
    leanh::lean_dec(v___y_3072_);
    leanh::lean_dec_ref(v___y_3071_);
    leanh::lean_dec(v___y_3070_);
    leanh::lean_dec_ref(v___y_3069_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(
    mut v_msgData_3075_: *mut leanh::LeanObject,
    mut v___y_3076_: *mut leanh::LeanObject,
    mut v___y_3077_: *mut leanh::LeanObject,
    mut v___y_3078_: *mut leanh::LeanObject,
    mut v___y_3079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3081_ = lean_st_ref_get(v___y_3079_);
    v_env_3082_ = leanh::lean_ctor_get(v___x_3081_, 0);
    leanh::lean_inc_ref(v_env_3082_);
    leanh::lean_dec(v___x_3081_);
    v___x_3083_ = lean_st_ref_get(v___y_3077_);
    v_mctx_3084_ = leanh::lean_ctor_get(v___x_3083_, 0);
    leanh::lean_inc_ref(v_mctx_3084_);
    leanh::lean_dec(v___x_3083_);
    v_lctx_3085_ = leanh::lean_ctor_get(v___y_3076_, 2);
    v_options_3086_ = leanh::lean_ctor_get(v___y_3078_, 2);
    leanh::lean_inc_ref(v_options_3086_);
    leanh::lean_inc_ref(v_lctx_3085_);
    v___x_3087_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3087_, 0, v_env_3082_);
    leanh::lean_ctor_set(v___x_3087_, 1, v_mctx_3084_);
    leanh::lean_ctor_set(v___x_3087_, 2, v_lctx_3085_);
    leanh::lean_ctor_set(v___x_3087_, 3, v_options_3086_);
    v___x_3088_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3088_, 0, v___x_3087_);
    leanh::lean_ctor_set(v___x_3088_, 1, v_msgData_3075_);
    v___x_3089_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3089_, 0, v___x_3088_);
    return v___x_3089_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5___boxed(
    mut v_msgData_3090_: *mut leanh::LeanObject,
    mut v___y_3091_: *mut leanh::LeanObject,
    mut v___y_3092_: *mut leanh::LeanObject,
    mut v___y_3093_: *mut leanh::LeanObject,
    mut v___y_3094_: *mut leanh::LeanObject,
    mut v___y_3095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3096_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(v_msgData_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
    leanh::lean_dec(v___y_3094_);
    leanh::lean_dec_ref(v___y_3093_);
    leanh::lean_dec(v___y_3092_);
    leanh::lean_dec_ref(v___y_3091_);
    return v_res_3096_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(
    mut v_msg_3097_: *mut leanh::LeanObject,
    mut v___y_3098_: *mut leanh::LeanObject,
    mut v___y_3099_: *mut leanh::LeanObject,
    mut v___y_3100_: *mut leanh::LeanObject,
    mut v___y_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3108_: u8 = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3103_ = leanh::lean_ctor_get(v___y_3100_, 5);
                v___x_3104_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4_spec__5(v_msg_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
                v_a_3105_ = leanh::lean_ctor_get(v___x_3104_, 0);
                v_isSharedCheck_3113_ = (!leanh::lean_is_exclusive(v___x_3104_)) as u8;
                if v_isSharedCheck_3113_ == 0 {
                    v___x_3107_ = v___x_3104_;
                    v_isShared_3108_ = v_isSharedCheck_3113_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3105_);
                    leanh::lean_dec(v___x_3104_);
                    v___x_3107_ = leanh::lean_box(0);
                    v_isShared_3108_ = v_isSharedCheck_3113_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3103_);
                v___x_3109_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3109_, 0, v_ref_3103_);
                leanh::lean_ctor_set(v___x_3109_, 1, v_a_3105_);
                if v_isShared_3108_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3107_, 1);
                    leanh::lean_ctor_set(v___x_3107_, 0, v___x_3109_);
                    v___x_3111_ = v___x_3107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
                    v___x_3111_ = v_reuseFailAlloc_3112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg___boxed(
    mut v_msg_3114_: *mut leanh::LeanObject,
    mut v___y_3115_: *mut leanh::LeanObject,
    mut v___y_3116_: *mut leanh::LeanObject,
    mut v___y_3117_: *mut leanh::LeanObject,
    mut v___y_3118_: *mut leanh::LeanObject,
    mut v___y_3119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3120_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(
        v_msg_3114_,
        v___y_3115_,
        v___y_3116_,
        v___y_3117_,
        v___y_3118_,
    );
    leanh::lean_dec(v___y_3118_);
    leanh::lean_dec_ref(v___y_3117_);
    leanh::lean_dec(v___y_3116_);
    leanh::lean_dec_ref(v___y_3115_);
    return v_res_3120_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(
    mut v_ref_3121_: *mut leanh::LeanObject,
    mut v_msg_3122_: *mut leanh::LeanObject,
    mut v___y_3123_: *mut leanh::LeanObject,
    mut v___y_3124_: *mut leanh::LeanObject,
    mut v___y_3125_: *mut leanh::LeanObject,
    mut v___y_3126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3140_: u8 = 0;
    let mut v_cancelTk_x3f_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3142_: u8 = 0;
    let mut v_inheritedTraceOptions_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3128_ = leanh::lean_ctor_get(v___y_3125_, 0);
    v_fileMap_3129_ = leanh::lean_ctor_get(v___y_3125_, 1);
    v_options_3130_ = leanh::lean_ctor_get(v___y_3125_, 2);
    v_currRecDepth_3131_ = leanh::lean_ctor_get(v___y_3125_, 3);
    v_maxRecDepth_3132_ = leanh::lean_ctor_get(v___y_3125_, 4);
    v_ref_3133_ = leanh::lean_ctor_get(v___y_3125_, 5);
    v_currNamespace_3134_ = leanh::lean_ctor_get(v___y_3125_, 6);
    v_openDecls_3135_ = leanh::lean_ctor_get(v___y_3125_, 7);
    v_initHeartbeats_3136_ = leanh::lean_ctor_get(v___y_3125_, 8);
    v_maxHeartbeats_3137_ = leanh::lean_ctor_get(v___y_3125_, 9);
    v_quotContext_3138_ = leanh::lean_ctor_get(v___y_3125_, 10);
    v_currMacroScope_3139_ = leanh::lean_ctor_get(v___y_3125_, 11);
    v_diag_3140_ = leanh::lean_ctor_get_uint8(
        v___y_3125_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3141_ = leanh::lean_ctor_get(v___y_3125_, 12);
    v_suppressElabErrors_3142_ = leanh::lean_ctor_get_uint8(
        v___y_3125_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3143_ = leanh::lean_ctor_get(v___y_3125_, 13);
    v_ref_3144_ = l_Lean_replaceRef(v_ref_3121_, v_ref_3133_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3143_);
    leanh::lean_inc(v_cancelTk_x3f_3141_);
    leanh::lean_inc(v_currMacroScope_3139_);
    leanh::lean_inc(v_quotContext_3138_);
    leanh::lean_inc(v_maxHeartbeats_3137_);
    leanh::lean_inc(v_initHeartbeats_3136_);
    leanh::lean_inc(v_openDecls_3135_);
    leanh::lean_inc(v_currNamespace_3134_);
    leanh::lean_inc(v_maxRecDepth_3132_);
    leanh::lean_inc(v_currRecDepth_3131_);
    leanh::lean_inc_ref(v_options_3130_);
    leanh::lean_inc_ref(v_fileMap_3129_);
    leanh::lean_inc_ref(v_fileName_3128_);
    v___x_3145_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3145_, 0, v_fileName_3128_);
    leanh::lean_ctor_set(v___x_3145_, 1, v_fileMap_3129_);
    leanh::lean_ctor_set(v___x_3145_, 2, v_options_3130_);
    leanh::lean_ctor_set(v___x_3145_, 3, v_currRecDepth_3131_);
    leanh::lean_ctor_set(v___x_3145_, 4, v_maxRecDepth_3132_);
    leanh::lean_ctor_set(v___x_3145_, 5, v_ref_3144_);
    leanh::lean_ctor_set(v___x_3145_, 6, v_currNamespace_3134_);
    leanh::lean_ctor_set(v___x_3145_, 7, v_openDecls_3135_);
    leanh::lean_ctor_set(v___x_3145_, 8, v_initHeartbeats_3136_);
    leanh::lean_ctor_set(v___x_3145_, 9, v_maxHeartbeats_3137_);
    leanh::lean_ctor_set(v___x_3145_, 10, v_quotContext_3138_);
    leanh::lean_ctor_set(v___x_3145_, 11, v_currMacroScope_3139_);
    leanh::lean_ctor_set(v___x_3145_, 12, v_cancelTk_x3f_3141_);
    leanh::lean_ctor_set(v___x_3145_, 13, v_inheritedTraceOptions_3143_);
    leanh::lean_ctor_set_uint8(
        v___x_3145_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3140_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3145_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3142_,
    );
    v___x_3146_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(
        v_msg_3122_,
        v___y_3123_,
        v___y_3124_,
        v___x_3145_,
        v___y_3126_,
    );
    leanh::lean_dec_ref_known(v___x_3145_, 14);
    return v___x_3146_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg___boxed(
    mut v_ref_3147_: *mut leanh::LeanObject,
    mut v_msg_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
    mut v___y_3153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3154_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3147_, v_msg_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
    leanh::lean_dec(v___y_3152_);
    leanh::lean_dec_ref(v___y_3151_);
    leanh::lean_dec(v___y_3150_);
    leanh::lean_dec_ref(v___y_3149_);
    leanh::lean_dec(v_ref_3147_);
    return v_res_3154_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(
    mut v_ref_3155_: *mut leanh::LeanObject,
    mut v_msg_3156_: *mut leanh::LeanObject,
    mut v_declHint_3157_: *mut leanh::LeanObject,
    mut v___y_3158_: *mut leanh::LeanObject,
    mut v___y_3159_: *mut leanh::LeanObject,
    mut v___y_3160_: *mut leanh::LeanObject,
    mut v___y_3161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3163_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_3156_, v_declHint_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
    v_a_3164_ = leanh::lean_ctor_get(v___x_3163_, 0);
    leanh::lean_inc(v_a_3164_);
    leanh::lean_dec_ref(v___x_3163_);
    v___x_3165_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3155_, v_a_3164_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
    return v___x_3165_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg___boxed(
    mut v_ref_3166_: *mut leanh::LeanObject,
    mut v_msg_3167_: *mut leanh::LeanObject,
    mut v_declHint_3168_: *mut leanh::LeanObject,
    mut v___y_3169_: *mut leanh::LeanObject,
    mut v___y_3170_: *mut leanh::LeanObject,
    mut v___y_3171_: *mut leanh::LeanObject,
    mut v___y_3172_: *mut leanh::LeanObject,
    mut v___y_3173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3174_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_3166_, v_msg_3167_, v_declHint_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
    leanh::lean_dec(v___y_3172_);
    leanh::lean_dec_ref(v___y_3171_);
    leanh::lean_dec(v___y_3170_);
    leanh::lean_dec_ref(v___y_3169_);
    leanh::lean_dec(v_ref_3166_);
    return v_res_3174_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3176_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__0;
    v___x_3177_ = l_Lean_stringToMessageData(v___x_3176_);
    return v___x_3177_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3179_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__2;
    v___x_3180_ = l_Lean_stringToMessageData(v___x_3179_);
    return v___x_3180_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(
    mut v_ref_3181_: *mut leanh::LeanObject,
    mut v_constName_3182_: *mut leanh::LeanObject,
    mut v___y_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
    mut v___y_3186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3188_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
    v___x_3189_ = 0;
    leanh::lean_inc(v_constName_3182_);
    v___x_3190_ = l_Lean_MessageData_ofConstName(v_constName_3182_, v___x_3189_);
    v___x_3191_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3191_, 0, v___x_3188_);
    leanh::lean_ctor_set(v___x_3191_, 1, v___x_3190_);
    v___x_3192_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
    v___x_3193_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3193_, 0, v___x_3191_);
    leanh::lean_ctor_set(v___x_3193_, 1, v___x_3192_);
    v___x_3194_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_3181_, v___x_3193_, v_constName_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
    return v___x_3194_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___boxed(
    mut v_ref_3195_: *mut leanh::LeanObject,
    mut v_constName_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
    mut v___y_3198_: *mut leanh::LeanObject,
    mut v___y_3199_: *mut leanh::LeanObject,
    mut v___y_3200_: *mut leanh::LeanObject,
    mut v___y_3201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3202_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_3195_, v_constName_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
    leanh::lean_dec(v___y_3200_);
    leanh::lean_dec_ref(v___y_3199_);
    leanh::lean_dec(v___y_3198_);
    leanh::lean_dec_ref(v___y_3197_);
    leanh::lean_dec(v_ref_3195_);
    return v_res_3202_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(
    mut v_constName_3203_: *mut leanh::LeanObject,
    mut v___y_3204_: *mut leanh::LeanObject,
    mut v___y_3205_: *mut leanh::LeanObject,
    mut v___y_3206_: *mut leanh::LeanObject,
    mut v___y_3207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3209_ = leanh::lean_ctor_get(v___y_3206_, 5);
    v___x_3210_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_3209_, v_constName_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
    return v___x_3210_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg___boxed(
    mut v_constName_3211_: *mut leanh::LeanObject,
    mut v___y_3212_: *mut leanh::LeanObject,
    mut v___y_3213_: *mut leanh::LeanObject,
    mut v___y_3214_: *mut leanh::LeanObject,
    mut v___y_3215_: *mut leanh::LeanObject,
    mut v___y_3216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3217_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
    leanh::lean_dec(v___y_3215_);
    leanh::lean_dec_ref(v___y_3214_);
    leanh::lean_dec(v___y_3213_);
    leanh::lean_dec_ref(v___y_3212_);
    return v_res_3217_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(
    mut v_constName_3218_: *mut leanh::LeanObject,
    mut v___y_3219_: *mut leanh::LeanObject,
    mut v___y_3220_: *mut leanh::LeanObject,
    mut v___y_3221_: *mut leanh::LeanObject,
    mut v___y_3222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: u8 = 0;
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3224_ = lean_st_ref_get(v___y_3222_);
                v_env_3225_ = leanh::lean_ctor_get(v___x_3224_, 0);
                leanh::lean_inc_ref(v_env_3225_);
                leanh::lean_dec(v___x_3224_);
                v___x_3226_ = 0;
                leanh::lean_inc(v_constName_3218_);
                v___x_3227_ =
                    l_Lean_Environment_find_x3f(v_env_3225_, v_constName_3218_, v___x_3226_);
                if leanh::lean_obj_tag(v___x_3227_) == 0 {
                    v___x_3228_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
                    return v___x_3228_;
                } else {
                    leanh::lean_dec(v_constName_3218_);
                    v_val_3229_ = leanh::lean_ctor_get(v___x_3227_, 0);
                    v_isSharedCheck_3236_ = (!leanh::lean_is_exclusive(v___x_3227_)) as u8;
                    if v_isSharedCheck_3236_ == 0 {
                        v___x_3231_ = v___x_3227_;
                        v_isShared_3232_ = v_isSharedCheck_3236_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3229_);
                        leanh::lean_dec(v___x_3227_);
                        v___x_3231_ = leanh::lean_box(0);
                        v_isShared_3232_ = v_isSharedCheck_3236_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3232_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3231_, 0);
                    v___x_3234_ = v___x_3231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3235_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_val_3229_);
                    v___x_3234_ = v_reuseFailAlloc_3235_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3___boxed(
    mut v_constName_3237_: *mut leanh::LeanObject,
    mut v___y_3238_: *mut leanh::LeanObject,
    mut v___y_3239_: *mut leanh::LeanObject,
    mut v___y_3240_: *mut leanh::LeanObject,
    mut v___y_3241_: *mut leanh::LeanObject,
    mut v___y_3242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3243_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(
        v_constName_3237_,
        v___y_3238_,
        v___y_3239_,
        v___y_3240_,
        v___y_3241_,
    );
    leanh::lean_dec(v___y_3241_);
    leanh::lean_dec_ref(v___y_3240_);
    leanh::lean_dec(v___y_3239_);
    leanh::lean_dec_ref(v___y_3238_);
    return v_res_3243_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(
    mut v_b_3244_: *mut leanh::LeanObject,
    mut v_arg_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
    mut v___y_3248_: *mut leanh::LeanObject,
    mut v___y_3249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Lean_Expr_app___override(v_b_3244_, v_arg_3245_);
    v___x_3252_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3252_, 0, v___x_3251_);
    v___x_3253_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3253_, 0, v___x_3252_);
    return v___x_3253_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1___boxed(
    mut v_b_3254_: *mut leanh::LeanObject,
    mut v_arg_3255_: *mut leanh::LeanObject,
    mut v___y_3256_: *mut leanh::LeanObject,
    mut v___y_3257_: *mut leanh::LeanObject,
    mut v___y_3258_: *mut leanh::LeanObject,
    mut v___y_3259_: *mut leanh::LeanObject,
    mut v___y_3260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_3254_, v_arg_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
    leanh::lean_dec(v___y_3259_);
    leanh::lean_dec_ref(v___y_3258_);
    leanh::lean_dec(v___y_3257_);
    leanh::lean_dec_ref(v___y_3256_);
    return v_res_3261_;
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(
    mut v_x_3262_: *mut leanh::LeanObject,
    mut v_b_3263_: *mut leanh::LeanObject,
    mut v___y_3264_: *mut leanh::LeanObject,
    mut v___y_3265_: *mut leanh::LeanObject,
    mut v___y_3266_: *mut leanh::LeanObject,
    mut v___y_3267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3269_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3269_, 0, v_b_3263_);
    return v___x_3269_;
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1___boxed(
    mut v_x_3270_: *mut leanh::LeanObject,
    mut v_b_3271_: *mut leanh::LeanObject,
    mut v___y_3272_: *mut leanh::LeanObject,
    mut v___y_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: *mut leanh::LeanObject,
    mut v___y_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3277_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__1(
        v_x_3270_,
        v_b_3271_,
        v___y_3272_,
        v___y_3273_,
        v___y_3274_,
        v___y_3275_,
    );
    leanh::lean_dec(v___y_3275_);
    leanh::lean_dec_ref(v___y_3274_);
    leanh::lean_dec(v___y_3273_);
    leanh::lean_dec_ref(v___y_3272_);
    leanh::lean_dec_ref(v_x_3270_);
    return v_res_3277_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3278_ = leanh::lean_box(0);
    v_dummy_3279_ = l_Lean_Expr_sort___override(v___x_3278_);
    return v_dummy_3279_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(
    mut v_upperBound_3281_: *mut leanh::LeanObject,
    mut v_params_3282_: *mut leanh::LeanObject,
    mut v___x_3283_: *mut leanh::LeanObject,
    mut v_ctx_3284_: *mut leanh::LeanObject,
    mut v_builtin_3285_: u8,
    mut v_force_3286_: u8,
    mut v_a_3287_: *mut leanh::LeanObject,
    mut v_b_3288_: *mut leanh::LeanObject,
    mut v___y_3289_: *mut leanh::LeanObject,
    mut v___y_3290_: *mut leanh::LeanObject,
    mut v___y_3291_: *mut leanh::LeanObject,
    mut v___y_3292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v_a_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut v_a_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3312_: u8 = 0;
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3316_: u8 = 0;
    let mut v___x_3317_: u8 = 0;
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3317_ = lean_nat_dec_lt(v_a_3287_, v_upperBound_3281_);
                if v___x_3317_ == 0 {
                    leanh::lean_dec(v_a_3287_);
                    leanh::lean_dec_ref(v_ctx_3284_);
                    v___x_3318_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3318_, 0, v_b_3288_);
                    return v___x_3318_;
                } else {
                    v___x_3319_ = l_Lean_instInhabitedExpr;
                    v___x_3320_ = lean_array_get_borrowed(v___x_3319_, v_params_3282_, v_a_3287_);
                    leanh::lean_inc(v___y_3292_);
                    leanh::lean_inc_ref(v___y_3291_);
                    leanh::lean_inc(v___y_3290_);
                    leanh::lean_inc_ref(v___y_3289_);
                    leanh::lean_inc(v___x_3320_);
                    v___x_3321_ = lean_infer_type(
                        v___x_3320_,
                        v___y_3289_,
                        v___y_3290_,
                        v___y_3291_,
                        v___y_3292_,
                    );
                    if leanh::lean_obj_tag(v___x_3321_) == 0 {
                        v_a_3322_ = leanh::lean_ctor_get(v___x_3321_, 0);
                        leanh::lean_inc(v_a_3322_);
                        leanh::lean_dec_ref_known(v___x_3321_, 1);
                        v___f_3323_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0;
                        v___x_3324_ = 0;
                        v___x_3325_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_3322_, v___f_3323_, v___x_3324_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
                        if leanh::lean_obj_tag(v___x_3325_) == 0 {
                            v_a_3326_ = leanh::lean_ctor_get(v___x_3325_, 0);
                            leanh::lean_inc(v_a_3326_);
                            leanh::lean_dec_ref_known(v___x_3325_, 1);
                            v___x_3327_ =
                                lean_array_get_borrowed(v___x_3319_, v___x_3283_, v_a_3287_);
                            v___x_3328_ =
                                l_Lean_ParserCompiler_Context_tyName___redArg(v_ctx_3284_);
                            v___x_3329_ = l_Lean_Expr_isConstOf(v_a_3326_, v___x_3328_);
                            leanh::lean_dec(v___x_3328_);
                            leanh::lean_dec(v_a_3326_);
                            if v___x_3329_ == 0 {
                                leanh::lean_inc(v___x_3327_);
                                v___x_3330_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_3288_, v___x_3327_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
                                v___y_3295_ = v___x_3330_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v___x_3327_);
                                leanh::lean_inc_ref(v_ctx_3284_);
                                v___x_3331_ = l_Lean_ParserCompiler_compileParserExpr___redArg(
                                    v_ctx_3284_,
                                    v_builtin_3285_,
                                    v_force_3286_,
                                    v___x_3327_,
                                    v___y_3289_,
                                    v___y_3290_,
                                    v___y_3291_,
                                    v___y_3292_,
                                );
                                if leanh::lean_obj_tag(v___x_3331_) == 0 {
                                    v_a_3332_ = leanh::lean_ctor_get(v___x_3331_, 0);
                                    leanh::lean_inc(v_a_3332_);
                                    leanh::lean_dec_ref_known(v___x_3331_, 1);
                                    v___x_3333_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___lam__1(v_b_3288_, v_a_3332_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
                                    v___y_3295_ = v___x_3333_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_b_3288_);
                                    leanh::lean_dec(v_a_3287_);
                                    leanh::lean_dec_ref(v_ctx_3284_);
                                    return v___x_3331_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_3288_);
                            leanh::lean_dec(v_a_3287_);
                            leanh::lean_dec_ref(v_ctx_3284_);
                            return v___x_3325_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_3288_);
                        leanh::lean_dec(v_a_3287_);
                        leanh::lean_dec_ref(v_ctx_3284_);
                        return v___x_3321_;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_3295_) == 0 {
                    v_a_3296_ = leanh::lean_ctor_get(v___y_3295_, 0);
                    v_isSharedCheck_3308_ = (!leanh::lean_is_exclusive(v___y_3295_)) as u8;
                    if v_isSharedCheck_3308_ == 0 {
                        v___x_3298_ = v___y_3295_;
                        v_isShared_3299_ = v_isSharedCheck_3308_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3296_);
                        leanh::lean_dec(v___y_3295_);
                        v___x_3298_ = leanh::lean_box(0);
                        v_isShared_3299_ = v_isSharedCheck_3308_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3287_);
                    leanh::lean_dec_ref(v_ctx_3284_);
                    v_a_3309_ = leanh::lean_ctor_get(v___y_3295_, 0);
                    v_isSharedCheck_3316_ = (!leanh::lean_is_exclusive(v___y_3295_)) as u8;
                    if v_isSharedCheck_3316_ == 0 {
                        v___x_3311_ = v___y_3295_;
                        v_isShared_3312_ = v_isSharedCheck_3316_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3309_);
                        leanh::lean_dec(v___y_3295_);
                        v___x_3311_ = leanh::lean_box(0);
                        v_isShared_3312_ = v_isSharedCheck_3316_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3296_) == 0 {
                    leanh::lean_dec(v_a_3287_);
                    leanh::lean_dec_ref(v_ctx_3284_);
                    v_a_3300_ = leanh::lean_ctor_get(v_a_3296_, 0);
                    leanh::lean_inc(v_a_3300_);
                    leanh::lean_dec_ref_known(v_a_3296_, 1);
                    if v_isShared_3299_ == 0 {
                        leanh::lean_ctor_set(v___x_3298_, 0, v_a_3300_);
                        v___x_3302_ = v___x_3298_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3303_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3300_);
                        v___x_3302_ = v_reuseFailAlloc_3303_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3298_);
                    v_a_3304_ = leanh::lean_ctor_get(v_a_3296_, 0);
                    leanh::lean_inc(v_a_3304_);
                    leanh::lean_dec_ref_known(v_a_3296_, 1);
                    v___x_3305_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3306_ = lean_nat_add(v_a_3287_, v___x_3305_);
                    leanh::lean_dec(v_a_3287_);
                    v_a_3287_ = v___x_3306_;
                    v_b_3288_ = v_a_3304_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_3302_;
            }
            4 => {
                if v_isShared_3312_ == 0 {
                    v___x_3314_ = v___x_3311_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3315_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
                    v___x_3314_ = v_reuseFailAlloc_3315_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_ctx_3335_: *mut leanh::LeanObject,
    mut v_builtin_3336_: u8,
    mut v_force_3337_: u8,
    mut v___x_3338_: *mut leanh::LeanObject,
    mut v_params_3339_: *mut leanh::LeanObject,
    mut v_x_3340_: *mut leanh::LeanObject,
    mut v___y_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
    mut v___y_3344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dummy_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_dummy_3346_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0_once
                    ),
                    _init_l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___closed__0,
                );
                v_nargs_3347_ = l_Lean_Expr_getAppNumArgs(v_a_3334_);
                leanh::lean_inc(v_nargs_3347_);
                v___x_3348_ = lean_mk_array(v_nargs_3347_, v_dummy_3346_);
                v___x_3349_ = leanh::lean_unsigned_to_nat(1);
                v___x_3350_ = lean_nat_sub(v_nargs_3347_, v___x_3349_);
                leanh::lean_dec(v_nargs_3347_);
                v___x_3351_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_a_3334_,
                    v___x_3348_,
                    v___x_3350_,
                );
                v___x_3356_ = lean_array_get_size(v_params_3339_);
                v___x_3357_ = lean_array_get_size(v___x_3351_);
                v___x_3358_ = lean_nat_dec_le(v___x_3356_, v___x_3357_);
                if v___x_3358_ == 0 {
                    v___y_3353_ = v___x_3357_;
                    state = 1;
                    continue;
                } else {
                    v___y_3353_ = v___x_3356_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3354_ = leanh::lean_unsigned_to_nat(0);
                v___x_3355_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v___y_3353_, v_params_3339_, v___x_3351_, v_ctx_3335_, v_builtin_3336_, v_force_3337_, v___x_3354_, v___x_3338_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
                leanh::lean_dec_ref(v___x_3351_);
                leanh::lean_dec(v___y_3353_);
                return v___x_3355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed(
    mut v_a_3359_: *mut leanh::LeanObject,
    mut v_ctx_3360_: *mut leanh::LeanObject,
    mut v_builtin_3361_: *mut leanh::LeanObject,
    mut v_force_3362_: *mut leanh::LeanObject,
    mut v___x_3363_: *mut leanh::LeanObject,
    mut v_params_3364_: *mut leanh::LeanObject,
    mut v_x_3365_: *mut leanh::LeanObject,
    mut v___y_3366_: *mut leanh::LeanObject,
    mut v___y_3367_: *mut leanh::LeanObject,
    mut v___y_3368_: *mut leanh::LeanObject,
    mut v___y_3369_: *mut leanh::LeanObject,
    mut v___y_3370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_boxed_3371_: u8 = 0;
    let mut v_force_boxed_3372_: u8 = 0;
    let mut v_res_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3371_ = (leanh::lean_unbox(v_builtin_3361_) as u8);
    v_force_boxed_3372_ = (leanh::lean_unbox(v_force_3362_) as u8);
    v_res_3373_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2(
        v_a_3359_,
        v_ctx_3360_,
        v_builtin_boxed_3371_,
        v_force_boxed_3372_,
        v___x_3363_,
        v_params_3364_,
        v_x_3365_,
        v___y_3366_,
        v___y_3367_,
        v___y_3368_,
        v___y_3369_,
    );
    leanh::lean_dec(v___y_3369_);
    leanh::lean_dec_ref(v___y_3368_);
    leanh::lean_dec(v___y_3367_);
    leanh::lean_dec_ref(v___y_3366_);
    leanh::lean_dec_ref(v_x_3365_);
    leanh::lean_dec_ref(v_params_3364_);
    return v_res_3373_;
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed(
    mut v_ctx_3374_: *mut leanh::LeanObject,
    mut v_builtin_3375_: *mut leanh::LeanObject,
    mut v_force_3376_: *mut leanh::LeanObject,
    mut v_x_3377_: *mut leanh::LeanObject,
    mut v_b_3378_: *mut leanh::LeanObject,
    mut v___y_3379_: *mut leanh::LeanObject,
    mut v___y_3380_: *mut leanh::LeanObject,
    mut v___y_3381_: *mut leanh::LeanObject,
    mut v___y_3382_: *mut leanh::LeanObject,
    mut v___y_3383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_boxed_3384_: u8 = 0;
    let mut v_force_boxed_3385_: u8 = 0;
    let mut v_res_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3384_ = (leanh::lean_unbox(v_builtin_3375_) as u8);
    v_force_boxed_3385_ = (leanh::lean_unbox(v_force_3376_) as u8);
    v_res_3386_ = l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(
        v_ctx_3374_,
        v_builtin_boxed_3384_,
        v_force_boxed_3385_,
        v_x_3377_,
        v_b_3378_,
        v___y_3379_,
        v___y_3380_,
        v___y_3381_,
        v___y_3382_,
    );
    leanh::lean_dec(v___y_3382_);
    leanh::lean_dec_ref(v___y_3381_);
    leanh::lean_dec(v___y_3380_);
    leanh::lean_dec_ref(v___y_3379_);
    leanh::lean_dec_ref(v_x_3377_);
    return v_res_3386_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3397_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3397_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5_once),
        _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__5,
    );
    v___x_3399_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3399_, 0, v___x_3398_);
    return v___x_3399_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6),
        core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once),
        _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6,
    );
    v___x_3401_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3401_, 0, v___x_3400_);
    leanh::lean_ctor_set(v___x_3401_, 1, v___x_3400_);
    return v___x_3401_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3402_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6),
        core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6_once),
        _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__6,
    );
    v___x_3403_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_3403_, 0, v___x_3402_);
    leanh::lean_ctor_set(v___x_3403_, 1, v___x_3402_);
    leanh::lean_ctor_set(v___x_3403_, 2, v___x_3402_);
    leanh::lean_ctor_set(v___x_3403_, 3, v___x_3402_);
    leanh::lean_ctor_set(v___x_3403_, 4, v___x_3402_);
    leanh::lean_ctor_set(v___x_3403_, 5, v___x_3402_);
    return v___x_3403_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3405_ = l_Lean_ParserCompiler_compileParserExpr___redArg___closed__9;
    v___x_3406_ = l_Lean_stringToMessageData(v___x_3405_);
    return v___x_3406_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3408_ = l_Lean_ParserCompiler_compileParserExpr___redArg___closed__11;
    v___x_3409_ = l_Lean_stringToMessageData(v___x_3408_);
    return v___x_3409_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3411_ = l_Lean_ParserCompiler_compileParserExpr___redArg___closed__13;
    v___x_3412_ = l_Lean_stringToMessageData(v___x_3411_);
    return v___x_3412_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = l_Lean_ParserCompiler_compileParserExpr___redArg___closed__15;
    v___x_3415_ = l_Lean_stringToMessageData(v___x_3414_);
    return v___x_3415_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3417_ = l_Lean_ParserCompiler_compileParserExpr___redArg___closed__17;
    v___x_3418_ = l_Lean_stringToMessageData(v___x_3417_);
    return v___x_3418_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3425_ = l_Lean_ParserCompiler_compileParserExpr___redArg___closed__21;
    v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
    return v___x_3426_;
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg(
    mut v_ctx_3427_: *mut leanh::LeanObject,
    mut v_builtin_3428_: u8,
    mut v_force_3429_: u8,
    mut v_e_3430_: *mut leanh::LeanObject,
    mut v_a_3431_: *mut leanh::LeanObject,
    mut v_a_3432_: *mut leanh::LeanObject,
    mut v_a_3433_: *mut leanh::LeanObject,
    mut v_a_3434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: u8 = 0;
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: u8 = 0;
    let mut v___x_3457_: u8 = 0;
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: u8 = 0;
    let mut v___x_3463_: u8 = 0;
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varName_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_categoryAttr_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_combinatorAttr_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3508_: u8 = 0;
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3512_: u8 = 0;
    let mut v___y_3514_: u8 = 0;
    let mut v___y_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3527_: u8 = 0;
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: u8 = 0;
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3551_: u8 = 0;
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: u8 = 0;
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defn_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defn_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_builtinName_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3582_: u8 = 0;
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3586_: u8 = 0;
    let mut v_reuseFailAlloc_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut v_unused_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3591_: u8 = 0;
    let mut v_unused_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3596_: u8 = 0;
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_reuseFailAlloc_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut v___y_3604_: u8 = 0;
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3626_: u8 = 0;
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3643_: u8 = 0;
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: u8 = 0;
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: u8 = 0;
    let mut v_a_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3665_: u8 = 0;
    let mut v_val_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3436_ =
                    l_Lean_Meta_whnfCore(v_e_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
                if leanh::lean_obj_tag(v___x_3436_) == 0 {
                    v_a_3437_ = leanh::lean_ctor_get(v___x_3436_, 0);
                    leanh::lean_inc(v_a_3437_);
                    match leanh::lean_obj_tag(v_a_3437_) {
                        6 => {
                            leanh::lean_dec_ref_known(v___x_3436_, 1);
                            v___x_3453_ = leanh::lean_box((v_builtin_3428_) as usize);
                            v___x_3454_ = leanh::lean_box((v_force_3429_) as usize);
                            v___f_3455_ = leanh::lean_alloc_closure(
                                l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                3,
                            );
                            leanh::lean_closure_set(v___f_3455_, 0, v_ctx_3427_);
                            leanh::lean_closure_set(v___f_3455_, 1, v___x_3453_);
                            leanh::lean_closure_set(v___f_3455_, 2, v___x_3454_);
                            v___x_3456_ = 0;
                            v___x_3457_ = 1;
                            v___x_3458_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_3437_, v___f_3455_, v___x_3456_, v___x_3456_, v___x_3457_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
                            return v___x_3458_;
                        }
                        8 => {
                            leanh::lean_dec_ref_known(v___x_3436_, 1);
                            v___x_3459_ = leanh::lean_box((v_builtin_3428_) as usize);
                            v___x_3460_ = leanh::lean_box((v_force_3429_) as usize);
                            v___f_3461_ = leanh::lean_alloc_closure(
                                l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                3,
                            );
                            leanh::lean_closure_set(v___f_3461_, 0, v_ctx_3427_);
                            leanh::lean_closure_set(v___f_3461_, 1, v___x_3459_);
                            leanh::lean_closure_set(v___f_3461_, 2, v___x_3460_);
                            v___x_3462_ = 0;
                            v___x_3463_ = 1;
                            v___x_3464_ = l_Lean_Meta_mapLambdaLetTelescope___at___00Lean_ParserCompiler_compileParserExpr_spec__2(v_a_3437_, v___f_3461_, v___x_3462_, v___x_3462_, v___x_3463_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
                            return v___x_3464_;
                        }
                        1 => {
                            leanh::lean_dec_ref_known(v_a_3437_, 1);
                            leanh::lean_dec_ref(v_ctx_3427_);
                            return v___x_3436_;
                        }
                        _ => {
                            leanh::lean_dec_ref_known(v___x_3436_, 1);
                            v___x_3465_ = l_Lean_Expr_getAppFn(v_a_3437_);
                            if leanh::lean_obj_tag(v___x_3465_) == 4 {
                                v_declName_3466_ = leanh::lean_ctor_get(v___x_3465_, 0);
                                leanh::lean_inc(v_declName_3466_);
                                leanh::lean_dec_ref_known(v___x_3465_, 2);
                                v___x_3467_ = lean_st_ref_get(v_a_3434_);
                                v_env_3468_ = leanh::lean_ctor_get(v___x_3467_, 0);
                                leanh::lean_inc_ref_n(v_env_3468_, 2);
                                leanh::lean_dec(v___x_3467_);
                                v_varName_3469_ = leanh::lean_ctor_get(v_ctx_3427_, 0);
                                v_categoryAttr_3470_ = leanh::lean_ctor_get(v_ctx_3427_, 1);
                                v_combinatorAttr_3471_ =
                                    leanh::lean_ctor_get(v_ctx_3427_, 2);
                                v___x_3472_ =
                                    l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(
                                        v_combinatorAttr_3471_,
                                        v_env_3468_,
                                        v_declName_3466_,
                                    );
                                if leanh::lean_obj_tag(v___x_3472_) == 0 {
                                    leanh::lean_inc(v_varName_3469_);
                                    leanh::lean_inc_n(v_declName_3466_, 2);
                                    v___x_3473_ =
                                        l_Lean_Name_append(v_declName_3466_, v_varName_3469_);
                                    v___x_3474_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3(v_declName_3466_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
                                    if leanh::lean_obj_tag(v___x_3474_) == 0 {
                                        v_a_3475_ = leanh::lean_ctor_get(v___x_3474_, 0);
                                        leanh::lean_inc(v_a_3475_);
                                        leanh::lean_dec_ref_known(v___x_3474_, 1);
                                        v___f_3476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___closed__0;
                                        v___x_3477_ = l_Lean_ConstantInfo_type(v_a_3475_);
                                        v___x_3478_ = 0;
                                        leanh::lean_inc_ref(v___x_3477_);
                                        v___x_3479_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_3477_, v___f_3476_, v___x_3478_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
                                        if leanh::lean_obj_tag(v___x_3479_) == 0 {
                                            v_a_3480_ = leanh::lean_ctor_get(v___x_3479_, 0);
                                            leanh::lean_inc(v_a_3480_);
                                            leanh::lean_dec_ref_known(v___x_3479_, 1);
                                            leanh::lean_inc_ref(v_ctx_3427_);
                                            v___f_3481_ = leanh::lean_alloc_closure(l_Lean_ParserCompiler_compileParserExpr___redArg___lam__3___boxed as *mut core::ffi::c_void, 8, 1);
                                            leanh::lean_closure_set(
                                                v___f_3481_,
                                                0,
                                                v_ctx_3427_,
                                            );
                                            v___x_3654_ = l_Lean_ParserCompiler_compileParserExpr___redArg___closed__20;
                                            v___x_3655_ =
                                                l_Lean_Expr_isConstOf(v_a_3480_, v___x_3654_);
                                            if v___x_3655_ == 0 {
                                                v___x_3656_ = l_Lean_ParserCompiler_replaceParserTy___redArg___lam__0___closed__2;
                                                v___x_3657_ =
                                                    l_Lean_Expr_isConstOf(v_a_3480_, v___x_3656_);
                                                leanh::lean_dec(v_a_3480_);
                                                v___y_3604_ = v___x_3657_;
                                                state = 16;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_a_3480_);
                                                v___y_3604_ = v___x_3655_;
                                                state = 16;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_3477_);
                                            leanh::lean_dec(v_a_3475_);
                                            leanh::lean_dec(v___x_3473_);
                                            leanh::lean_dec_ref(v_env_3468_);
                                            leanh::lean_dec(v_declName_3466_);
                                            leanh::lean_dec(v_a_3437_);
                                            leanh::lean_dec_ref(v_ctx_3427_);
                                            return v___x_3479_;
                                        }
                                    } else {
                                        leanh::lean_dec(v___x_3473_);
                                        leanh::lean_dec_ref(v_env_3468_);
                                        leanh::lean_dec(v_declName_3466_);
                                        leanh::lean_dec(v_a_3437_);
                                        leanh::lean_dec_ref(v_ctx_3427_);
                                        v_a_3658_ = leanh::lean_ctor_get(v___x_3474_, 0);
                                        v_isSharedCheck_3665_ =
                                            (!leanh::lean_is_exclusive(v___x_3474_)) as u8;
                                        if v_isSharedCheck_3665_ == 0 {
                                            v___x_3660_ = v___x_3474_;
                                            v_isShared_3661_ = v_isSharedCheck_3665_;
                                            state = 21;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3658_);
                                            leanh::lean_dec(v___x_3474_);
                                            v___x_3660_ = leanh::lean_box(0);
                                            v_isShared_3661_ = v_isSharedCheck_3665_;
                                            state = 21;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_env_3468_);
                                    leanh::lean_dec(v_declName_3466_);
                                    v_val_3666_ = leanh::lean_ctor_get(v___x_3472_, 0);
                                    leanh::lean_inc(v_val_3666_);
                                    leanh::lean_dec_ref_known(v___x_3472_, 1);
                                    v_p_3439_ = v_val_3666_;
                                    v___y_3440_ = v_a_3431_;
                                    v___y_3441_ = v_a_3432_;
                                    v___y_3442_ = v_a_3433_;
                                    v___y_3443_ = v_a_3434_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_3465_);
                                leanh::lean_dec_ref(v_ctx_3427_);
                                v___x_3667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22_once), _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__22);
                                v___x_3668_ = l_Lean_MessageData_ofExpr(v_a_3437_);
                                v___x_3669_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3669_, 0, v___x_3667_);
                                leanh::lean_ctor_set(v___x_3669_, 1, v___x_3668_);
                                v___x_3670_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
                                v___x_3671_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3671_, 0, v___x_3669_);
                                leanh::lean_ctor_set(v___x_3671_, 1, v___x_3670_);
                                v___x_3672_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_3671_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
                                return v___x_3672_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_ctx_3427_);
                    return v___x_3436_;
                }
            }
            1 => {
                v___x_3444_ = leanh::lean_box(0);
                v___x_3445_ = l_Lean_mkConst(v_p_3439_, v___x_3444_);
                leanh::lean_inc(v___y_3443_);
                leanh::lean_inc_ref(v___y_3442_);
                leanh::lean_inc(v___y_3441_);
                leanh::lean_inc_ref(v___y_3440_);
                leanh::lean_inc_ref(v___x_3445_);
                v___x_3446_ = lean_infer_type(
                    v___x_3445_,
                    v___y_3440_,
                    v___y_3441_,
                    v___y_3442_,
                    v___y_3443_,
                );
                if leanh::lean_obj_tag(v___x_3446_) == 0 {
                    v_a_3447_ = leanh::lean_ctor_get(v___x_3446_, 0);
                    leanh::lean_inc(v_a_3447_);
                    leanh::lean_dec_ref_known(v___x_3446_, 1);
                    v___x_3448_ = leanh::lean_box((v_builtin_3428_) as usize);
                    v___x_3449_ = leanh::lean_box((v_force_3429_) as usize);
                    v___f_3450_ = leanh::lean_alloc_closure(
                        l_Lean_ParserCompiler_compileParserExpr___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        12,
                        5,
                    );
                    leanh::lean_closure_set(v___f_3450_, 0, v_a_3437_);
                    leanh::lean_closure_set(v___f_3450_, 1, v_ctx_3427_);
                    leanh::lean_closure_set(v___f_3450_, 2, v___x_3448_);
                    leanh::lean_closure_set(v___f_3450_, 3, v___x_3449_);
                    leanh::lean_closure_set(v___f_3450_, 4, v___x_3445_);
                    v___x_3451_ = 0;
                    v___x_3452_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v_a_3447_, v___f_3450_, v___x_3451_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
                    return v___x_3452_;
                } else {
                    leanh::lean_dec_ref(v___x_3445_);
                    leanh::lean_dec(v_a_3437_);
                    leanh::lean_dec_ref(v_ctx_3427_);
                    return v___x_3446_;
                }
            }
            2 => {
                v___x_3489_ = l_Lean_ParserCompiler_compileParserExpr___redArg___closed__2;
                leanh::lean_inc(v___y_3488_);
                v___x_3490_ = lean_mk_syntax_ident(v___y_3488_);
                v___x_3491_ = lean_mk_syntax_ident(v___y_3483_);
                v___x_3492_ = leanh::lean_unsigned_to_nat(1);
                v___x_3493_ = lean_mk_empty_array_with_capacity(v___x_3492_);
                v___x_3494_ = lean_array_push(v___x_3493_, v___x_3491_);
                v___x_3495_ = l_Lean_ParserCompiler_compileParserExpr___redArg___closed__4;
                v___x_3496_ = leanh::lean_box(2);
                v___x_3497_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3497_, 0, v___x_3496_);
                leanh::lean_ctor_set(v___x_3497_, 1, v___x_3495_);
                leanh::lean_ctor_set(v___x_3497_, 2, v___x_3494_);
                v___x_3498_ = leanh::lean_unsigned_to_nat(2);
                v___x_3499_ = lean_mk_empty_array_with_capacity(v___x_3498_);
                v___x_3500_ = lean_array_push(v___x_3499_, v___x_3490_);
                v___x_3501_ = lean_array_push(v___x_3500_, v___x_3497_);
                v___x_3502_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3502_, 0, v___x_3496_);
                leanh::lean_ctor_set(v___x_3502_, 1, v___x_3489_);
                leanh::lean_ctor_set(v___x_3502_, 2, v___x_3501_);
                v___x_3503_ = 0;
                leanh::lean_inc(v___x_3473_);
                v___x_3504_ = l_Lean_Attribute_add(
                    v___x_3473_,
                    v___y_3488_,
                    v___x_3502_,
                    v___x_3503_,
                    v___y_3486_,
                    v___y_3487_,
                );
                if leanh::lean_obj_tag(v___x_3504_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3504_, 1);
                    v_p_3439_ = v___x_3473_;
                    v___y_3440_ = v___y_3484_;
                    v___y_3441_ = v___y_3485_;
                    v___y_3442_ = v___y_3486_;
                    v___y_3443_ = v___y_3487_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3473_);
                    leanh::lean_dec(v_a_3437_);
                    leanh::lean_dec_ref(v_ctx_3427_);
                    v_a_3505_ = leanh::lean_ctor_get(v___x_3504_, 0);
                    v_isSharedCheck_3512_ = (!leanh::lean_is_exclusive(v___x_3504_)) as u8;
                    if v_isSharedCheck_3512_ == 0 {
                        v___x_3507_ = v___x_3504_;
                        v_isShared_3508_ = v_isSharedCheck_3512_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3505_);
                        leanh::lean_dec(v___x_3504_);
                        v___x_3507_ = leanh::lean_box(0);
                        v_isShared_3508_ = v_isSharedCheck_3512_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3508_ == 0 {
                    v___x_3510_ = v___x_3507_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
                    v___x_3510_ = v_reuseFailAlloc_3511_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3510_;
            }
            5 => {
                leanh::lean_inc_ref_n(v_ctx_3427_, 2);
                v___x_3520_ =
                    l_Lean_ParserCompiler_replaceParserTy___redArg(v_ctx_3427_, v___y_3515_);
                leanh::lean_dec_ref(v___y_3515_);
                v___x_3521_ = l_Lean_ParserCompiler_compileParserExpr___redArg(
                    v_ctx_3427_,
                    v_builtin_3428_,
                    v_force_3429_,
                    v___x_3520_,
                    v___y_3516_,
                    v___y_3517_,
                    v___y_3518_,
                    v___y_3519_,
                );
                if leanh::lean_obj_tag(v___x_3521_) == 0 {
                    v_a_3522_ = leanh::lean_ctor_get(v___x_3521_, 0);
                    leanh::lean_inc(v_a_3522_);
                    leanh::lean_dec_ref_known(v___x_3521_, 1);
                    leanh::lean_inc_ref(v___x_3477_);
                    v___x_3523_ = l_Lean_Meta_forallTelescope___at___00Lean_ParserCompiler_parserNodeKind_x3f_spec__3___redArg(v___x_3477_, v___f_3481_, v___x_3478_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
                    if leanh::lean_obj_tag(v___x_3523_) == 0 {
                        v_a_3524_ = leanh::lean_ctor_get(v___x_3523_, 0);
                        v_isSharedCheck_3602_ =
                            (!leanh::lean_is_exclusive(v___x_3523_)) as u8;
                        if v_isSharedCheck_3602_ == 0 {
                            v___x_3526_ = v___x_3523_;
                            v_isShared_3527_ = v_isSharedCheck_3602_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3524_);
                            leanh::lean_dec(v___x_3523_);
                            v___x_3526_ = leanh::lean_box(0);
                            v_isShared_3527_ = v_isSharedCheck_3602_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3522_);
                        leanh::lean_dec_ref(v___x_3477_);
                        leanh::lean_dec(v_a_3475_);
                        leanh::lean_dec(v___x_3473_);
                        leanh::lean_dec(v_declName_3466_);
                        leanh::lean_dec(v_a_3437_);
                        leanh::lean_dec_ref(v_ctx_3427_);
                        return v___x_3523_;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_3481_);
                    leanh::lean_dec_ref(v___x_3477_);
                    leanh::lean_dec(v_a_3475_);
                    leanh::lean_dec(v___x_3473_);
                    leanh::lean_dec(v_declName_3466_);
                    leanh::lean_dec(v_a_3437_);
                    leanh::lean_dec_ref(v_ctx_3427_);
                    return v___x_3521_;
                }
            }
            6 => {
                v___x_3528_ = lean_st_ref_get(v___y_3519_);
                v_env_3529_ = leanh::lean_ctor_get(v___x_3528_, 0);
                leanh::lean_inc_ref(v_env_3529_);
                leanh::lean_dec(v___x_3528_);
                v___x_3530_ = leanh::lean_box(0);
                leanh::lean_inc_n(v___x_3473_, 2);
                v___x_3531_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3531_, 0, v___x_3473_);
                leanh::lean_ctor_set(v___x_3531_, 1, v___x_3530_);
                leanh::lean_ctor_set(v___x_3531_, 2, v_a_3524_);
                v___x_3532_ = leanh::lean_box(0);
                v___x_3533_ = 1;
                v___x_3534_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3534_, 0, v___x_3473_);
                leanh::lean_ctor_set(v___x_3534_, 1, v___x_3530_);
                v___x_3535_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_3535_, 0, v___x_3531_);
                leanh::lean_ctor_set(v___x_3535_, 1, v_a_3522_);
                leanh::lean_ctor_set(v___x_3535_, 2, v___x_3532_);
                leanh::lean_ctor_set(v___x_3535_, 3, v___x_3534_);
                leanh::lean_ctor_set_uint8(
                    v___x_3535_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_3533_,
                );
                if v_isShared_3527_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3526_, 1);
                    leanh::lean_ctor_set(v___x_3526_, 0, v___x_3535_);
                    v___x_3537_ = v___x_3526_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3601_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3535_);
                    v___x_3537_ = v_reuseFailAlloc_3601_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc(v_declName_3466_);
                v___x_3538_ = l_Lean_isMarkedMeta(v_env_3529_, v_declName_3466_);
                v___x_3539_ = l_Lean_addAndCompile(
                    v___x_3537_,
                    v___y_3514_,
                    v___x_3538_,
                    v___y_3518_,
                    v___y_3519_,
                );
                if leanh::lean_obj_tag(v___x_3539_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3539_, 1);
                    v___x_3540_ = lean_st_ref_take(v___y_3519_);
                    v_env_3541_ = leanh::lean_ctor_get(v___x_3540_, 0);
                    v_nextMacroScope_3542_ = leanh::lean_ctor_get(v___x_3540_, 1);
                    v_ngen_3543_ = leanh::lean_ctor_get(v___x_3540_, 2);
                    v_auxDeclNGen_3544_ = leanh::lean_ctor_get(v___x_3540_, 3);
                    v_traceState_3545_ = leanh::lean_ctor_get(v___x_3540_, 4);
                    v_messages_3546_ = leanh::lean_ctor_get(v___x_3540_, 6);
                    v_infoState_3547_ = leanh::lean_ctor_get(v___x_3540_, 7);
                    v_snapshotTasks_3548_ = leanh::lean_ctor_get(v___x_3540_, 8);
                    v_isSharedCheck_3591_ = (!leanh::lean_is_exclusive(v___x_3540_)) as u8;
                    if v_isSharedCheck_3591_ == 0 {
                        v_unused_3592_ = leanh::lean_ctor_get(v___x_3540_, 5);
                        leanh::lean_dec(v_unused_3592_);
                        v___x_3550_ = v___x_3540_;
                        v_isShared_3551_ = v_isSharedCheck_3591_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_3548_);
                        leanh::lean_inc(v_infoState_3547_);
                        leanh::lean_inc(v_messages_3546_);
                        leanh::lean_inc(v_traceState_3545_);
                        leanh::lean_inc(v_auxDeclNGen_3544_);
                        leanh::lean_inc(v_ngen_3543_);
                        leanh::lean_inc(v_nextMacroScope_3542_);
                        leanh::lean_inc(v_env_3541_);
                        leanh::lean_dec(v___x_3540_);
                        v___x_3550_ = leanh::lean_box(0);
                        v_isShared_3551_ = v_isSharedCheck_3591_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3477_);
                    leanh::lean_dec(v_a_3475_);
                    leanh::lean_dec(v___x_3473_);
                    leanh::lean_dec(v_declName_3466_);
                    leanh::lean_dec(v_a_3437_);
                    leanh::lean_dec_ref(v_ctx_3427_);
                    v_a_3593_ = leanh::lean_ctor_get(v___x_3539_, 0);
                    v_isSharedCheck_3600_ = (!leanh::lean_is_exclusive(v___x_3539_)) as u8;
                    if v_isSharedCheck_3600_ == 0 {
                        v___x_3595_ = v___x_3539_;
                        v_isShared_3596_ = v_isSharedCheck_3600_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3593_);
                        leanh::lean_dec(v___x_3539_);
                        v___x_3595_ = leanh::lean_box(0);
                        v_isShared_3596_ = v_isSharedCheck_3600_;
                        state = 14;
                        continue;
                    }
                }
            }
            8 => {
                leanh::lean_inc(v___x_3473_);
                leanh::lean_inc_ref(v_combinatorAttr_3471_);
                v___x_3552_ = l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(
                    v_combinatorAttr_3471_,
                    v_env_3541_,
                    v_declName_3466_,
                    v___x_3473_,
                );
                v___x_3553_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once
                    ),
                    _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7,
                );
                if v_isShared_3551_ == 0 {
                    leanh::lean_ctor_set(v___x_3550_, 5, v___x_3553_);
                    leanh::lean_ctor_set(v___x_3550_, 0, v___x_3552_);
                    v___x_3555_ = v___x_3550_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3590_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_nextMacroScope_3542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_ngen_3543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 3, v_auxDeclNGen_3544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_traceState_3545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 5, v___x_3553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 6, v_messages_3546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 7, v_infoState_3547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 8, v_snapshotTasks_3548_);
                    v___x_3555_ = v_reuseFailAlloc_3590_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3556_ = lean_st_ref_set(v___y_3519_, v___x_3555_);
                v___x_3557_ = lean_st_ref_take(v___y_3517_);
                v_mctx_3558_ = leanh::lean_ctor_get(v___x_3557_, 0);
                v_zetaDeltaFVarIds_3559_ = leanh::lean_ctor_get(v___x_3557_, 2);
                v_postponed_3560_ = leanh::lean_ctor_get(v___x_3557_, 3);
                v_diag_3561_ = leanh::lean_ctor_get(v___x_3557_, 4);
                v_isSharedCheck_3588_ = (!leanh::lean_is_exclusive(v___x_3557_)) as u8;
                if v_isSharedCheck_3588_ == 0 {
                    v_unused_3589_ = leanh::lean_ctor_get(v___x_3557_, 1);
                    leanh::lean_dec(v_unused_3589_);
                    v___x_3563_ = v___x_3557_;
                    v_isShared_3564_ = v_isSharedCheck_3588_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3561_);
                    leanh::lean_inc(v_postponed_3560_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3559_);
                    leanh::lean_inc(v_mctx_3558_);
                    leanh::lean_dec(v___x_3557_);
                    v___x_3563_ = leanh::lean_box(0);
                    v_isShared_3564_ = v_isSharedCheck_3588_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3565_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8_once
                    ),
                    _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__8,
                );
                if v_isShared_3564_ == 0 {
                    leanh::lean_ctor_set(v___x_3563_, 1, v___x_3565_);
                    v___x_3567_ = v___x_3563_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3587_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_mctx_3558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 1, v___x_3565_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3587_,
                        2,
                        v_zetaDeltaFVarIds_3559_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 3, v_postponed_3560_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_diag_3561_);
                    v___x_3567_ = v_reuseFailAlloc_3587_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3568_ = lean_st_ref_set(v___y_3517_, v___x_3567_);
                v___x_3569_ = l_Lean_Expr_isConst(v___x_3477_);
                leanh::lean_dec_ref(v___x_3477_);
                if v___x_3569_ == 0 {
                    leanh::lean_dec(v_a_3475_);
                    v_p_3439_ = v___x_3473_;
                    v___y_3440_ = v___y_3516_;
                    v___y_3441_ = v___y_3517_;
                    v___y_3442_ = v___y_3518_;
                    v___y_3443_ = v___y_3519_;
                    state = 1;
                    continue;
                } else {
                    v___x_3570_ = l_Lean_ConstantInfo_value_x21(v_a_3475_, v___x_3478_);
                    leanh::lean_dec(v_a_3475_);
                    v___x_3571_ = l_Lean_ParserCompiler_parserNodeKind_x3f(
                        v___x_3570_,
                        v___y_3516_,
                        v___y_3517_,
                        v___y_3518_,
                        v___y_3519_,
                    );
                    if leanh::lean_obj_tag(v___x_3571_) == 0 {
                        v_a_3572_ = leanh::lean_ctor_get(v___x_3571_, 0);
                        leanh::lean_inc(v_a_3572_);
                        leanh::lean_dec_ref_known(v___x_3571_, 1);
                        if leanh::lean_obj_tag(v_a_3572_) == 1 {
                            if v_builtin_3428_ == 0 {
                                v_defn_3573_ = leanh::lean_ctor_get(v_categoryAttr_3470_, 0);
                                v_val_3574_ = leanh::lean_ctor_get(v_a_3572_, 0);
                                leanh::lean_inc(v_val_3574_);
                                leanh::lean_dec_ref_known(v_a_3572_, 1);
                                v_name_3575_ = leanh::lean_ctor_get(v_defn_3573_, 1);
                                leanh::lean_inc(v_name_3575_);
                                v___y_3483_ = v_val_3574_;
                                v___y_3484_ = v___y_3516_;
                                v___y_3485_ = v___y_3517_;
                                v___y_3486_ = v___y_3518_;
                                v___y_3487_ = v___y_3519_;
                                v___y_3488_ = v_name_3575_;
                                state = 2;
                                continue;
                            } else {
                                v_defn_3576_ = leanh::lean_ctor_get(v_categoryAttr_3470_, 0);
                                v_val_3577_ = leanh::lean_ctor_get(v_a_3572_, 0);
                                leanh::lean_inc(v_val_3577_);
                                leanh::lean_dec_ref_known(v_a_3572_, 1);
                                v_builtinName_3578_ = leanh::lean_ctor_get(v_defn_3576_, 0);
                                leanh::lean_inc(v_builtinName_3578_);
                                v___y_3483_ = v_val_3577_;
                                v___y_3484_ = v___y_3516_;
                                v___y_3485_ = v___y_3517_;
                                v___y_3486_ = v___y_3518_;
                                v___y_3487_ = v___y_3519_;
                                v___y_3488_ = v_builtinName_3578_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3572_);
                            v_p_3439_ = v___x_3473_;
                            v___y_3440_ = v___y_3516_;
                            v___y_3441_ = v___y_3517_;
                            v___y_3442_ = v___y_3518_;
                            v___y_3443_ = v___y_3519_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3473_);
                        leanh::lean_dec(v_a_3437_);
                        leanh::lean_dec_ref(v_ctx_3427_);
                        v_a_3579_ = leanh::lean_ctor_get(v___x_3571_, 0);
                        v_isSharedCheck_3586_ =
                            (!leanh::lean_is_exclusive(v___x_3571_)) as u8;
                        if v_isSharedCheck_3586_ == 0 {
                            v___x_3581_ = v___x_3571_;
                            v_isShared_3582_ = v_isSharedCheck_3586_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3579_);
                            leanh::lean_dec(v___x_3571_);
                            v___x_3581_ = leanh::lean_box(0);
                            v_isShared_3582_ = v_isSharedCheck_3586_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            12 => {
                if v_isShared_3582_ == 0 {
                    v___x_3584_ = v___x_3581_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
                    v___x_3584_ = v_reuseFailAlloc_3585_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3584_;
            }
            14 => {
                if v_isShared_3596_ == 0 {
                    v___x_3598_ = v___x_3595_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
                    v___x_3598_ = v_reuseFailAlloc_3599_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3598_;
            }
            16 => {
                if v___y_3604_ == 0 {
                    leanh::lean_dec_ref(v___f_3481_);
                    leanh::lean_dec_ref(v___x_3477_);
                    leanh::lean_dec(v_a_3475_);
                    leanh::lean_dec(v___x_3473_);
                    leanh::lean_dec_ref(v_env_3468_);
                    leanh::lean_dec(v_declName_3466_);
                    leanh::lean_inc(v_a_3437_);
                    v___x_3605_ = l_Lean_Meta_unfoldDefinition_x3f(
                        v_a_3437_,
                        v___x_3478_,
                        v_a_3431_,
                        v_a_3432_,
                        v_a_3433_,
                        v_a_3434_,
                    );
                    if leanh::lean_obj_tag(v___x_3605_) == 0 {
                        v_a_3606_ = leanh::lean_ctor_get(v___x_3605_, 0);
                        leanh::lean_inc(v_a_3606_);
                        leanh::lean_dec_ref_known(v___x_3605_, 1);
                        if leanh::lean_obj_tag(v_a_3606_) == 1 {
                            leanh::lean_dec(v_a_3437_);
                            v_val_3607_ = leanh::lean_ctor_get(v_a_3606_, 0);
                            leanh::lean_inc(v_val_3607_);
                            leanh::lean_dec_ref_known(v_a_3606_, 1);
                            v_e_3430_ = v_val_3607_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_inc(v_varName_3469_);
                            leanh::lean_dec(v_a_3606_);
                            leanh::lean_dec_ref(v_ctx_3427_);
                            v___x_3609_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once), _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10);
                            v___x_3610_ = l_Lean_MessageData_ofName(v_varName_3469_);
                            v___x_3611_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3611_, 0, v___x_3609_);
                            leanh::lean_ctor_set(v___x_3611_, 1, v___x_3610_);
                            v___x_3612_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12_once), _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__12);
                            v___x_3613_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3613_, 0, v___x_3611_);
                            leanh::lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                            v___x_3614_ = l_Lean_MessageData_ofExpr(v_a_3437_);
                            v___x_3615_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3615_, 0, v___x_3613_);
                            leanh::lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                            v___x_3616_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
                            v___x_3617_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3617_, 0, v___x_3615_);
                            leanh::lean_ctor_set(v___x_3617_, 1, v___x_3616_);
                            v___x_3618_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_3617_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
                            return v___x_3618_;
                        }
                    } else {
                        leanh::lean_dec(v_a_3437_);
                        leanh::lean_dec_ref(v_ctx_3427_);
                        v_a_3619_ = leanh::lean_ctor_get(v___x_3605_, 0);
                        v_isSharedCheck_3626_ =
                            (!leanh::lean_is_exclusive(v___x_3605_)) as u8;
                        if v_isSharedCheck_3626_ == 0 {
                            v___x_3621_ = v___x_3605_;
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3619_);
                            leanh::lean_dec(v___x_3605_);
                            v___x_3621_ = leanh::lean_box(0);
                            v_isShared_3622_ = v_isSharedCheck_3626_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_a_3475_);
                    v___x_3627_ = l_Lean_ConstantInfo_value_x3f(v_a_3475_, v___x_3478_);
                    if leanh::lean_obj_tag(v___x_3627_) == 1 {
                        v_val_3628_ = leanh::lean_ctor_get(v___x_3627_, 0);
                        leanh::lean_inc(v_val_3628_);
                        leanh::lean_dec_ref_known(v___x_3627_, 1);
                        v___x_3629_ =
                            l_Lean_Environment_getModuleIdxFor_x3f(v_env_3468_, v_declName_3466_);
                        leanh::lean_dec_ref(v_env_3468_);
                        if leanh::lean_obj_tag(v___x_3629_) == 0 {
                            v___y_3514_ = v___y_3604_;
                            v___y_3515_ = v_val_3628_;
                            v___y_3516_ = v_a_3431_;
                            v___y_3517_ = v_a_3432_;
                            v___y_3518_ = v_a_3433_;
                            v___y_3519_ = v_a_3434_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v___x_3629_, 1);
                            if v_force_3429_ == 0 {
                                v___x_3630_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14_once), _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__14);
                                leanh::lean_inc(v_declName_3466_);
                                v___x_3631_ = l_Lean_MessageData_ofName(v_declName_3466_);
                                v___x_3632_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3632_, 0, v___x_3630_);
                                leanh::lean_ctor_set(v___x_3632_, 1, v___x_3631_);
                                v___x_3633_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16_once), _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__16);
                                v___x_3634_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3634_, 0, v___x_3632_);
                                leanh::lean_ctor_set(v___x_3634_, 1, v___x_3633_);
                                v___x_3635_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_3634_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
                                if leanh::lean_obj_tag(v___x_3635_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3635_, 1);
                                    v___y_3514_ = v___y_3604_;
                                    v___y_3515_ = v_val_3628_;
                                    v___y_3516_ = v_a_3431_;
                                    v___y_3517_ = v_a_3432_;
                                    v___y_3518_ = v_a_3433_;
                                    v___y_3519_ = v_a_3434_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_val_3628_);
                                    leanh::lean_dec_ref(v___f_3481_);
                                    leanh::lean_dec_ref(v___x_3477_);
                                    leanh::lean_dec(v_a_3475_);
                                    leanh::lean_dec(v___x_3473_);
                                    leanh::lean_dec(v_declName_3466_);
                                    leanh::lean_dec(v_a_3437_);
                                    leanh::lean_dec_ref(v_ctx_3427_);
                                    v_a_3636_ = leanh::lean_ctor_get(v___x_3635_, 0);
                                    v_isSharedCheck_3643_ =
                                        (!leanh::lean_is_exclusive(v___x_3635_)) as u8;
                                    if v_isSharedCheck_3643_ == 0 {
                                        v___x_3638_ = v___x_3635_;
                                        v_isShared_3639_ = v_isSharedCheck_3643_;
                                        state = 19;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3636_);
                                        leanh::lean_dec(v___x_3635_);
                                        v___x_3638_ = leanh::lean_box(0);
                                        v_isShared_3639_ = v_isSharedCheck_3643_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            } else {
                                v___y_3514_ = v___y_3604_;
                                v___y_3515_ = v_val_3628_;
                                v___y_3516_ = v_a_3431_;
                                v___y_3517_ = v_a_3432_;
                                v___y_3518_ = v_a_3433_;
                                v___y_3519_ = v_a_3434_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_inc(v_varName_3469_);
                        leanh::lean_dec(v___x_3627_);
                        leanh::lean_dec_ref(v___f_3481_);
                        leanh::lean_dec_ref(v___x_3477_);
                        leanh::lean_dec(v_a_3475_);
                        leanh::lean_dec(v___x_3473_);
                        leanh::lean_dec_ref(v_env_3468_);
                        leanh::lean_dec(v_declName_3466_);
                        leanh::lean_dec_ref(v_ctx_3427_);
                        v___x_3644_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10_once
                            ),
                            _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__10,
                        );
                        v___x_3645_ = l_Lean_MessageData_ofName(v_varName_3469_);
                        v___x_3646_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3646_, 0, v___x_3644_);
                        leanh::lean_ctor_set(v___x_3646_, 1, v___x_3645_);
                        v___x_3647_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18_once
                            ),
                            _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__18,
                        );
                        v___x_3648_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3648_, 0, v___x_3646_);
                        leanh::lean_ctor_set(v___x_3648_, 1, v___x_3647_);
                        v___x_3649_ = l_Lean_MessageData_ofExpr(v_a_3437_);
                        v___x_3650_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3650_, 0, v___x_3648_);
                        leanh::lean_ctor_set(v___x_3650_, 1, v___x_3649_);
                        v___x_3651_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
                        v___x_3652_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3652_, 0, v___x_3650_);
                        leanh::lean_ctor_set(v___x_3652_, 1, v___x_3651_);
                        v___x_3653_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(v___x_3652_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
                        return v___x_3653_;
                    }
                }
            }
            17 => {
                if v_isShared_3622_ == 0 {
                    v___x_3624_ = v___x_3621_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3625_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
                    v___x_3624_ = v_reuseFailAlloc_3625_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3624_;
            }
            19 => {
                if v_isShared_3639_ == 0 {
                    v___x_3641_ = v___x_3638_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3642_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
                    v___x_3641_ = v_reuseFailAlloc_3642_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3641_;
            }
            21 => {
                if v_isShared_3661_ == 0 {
                    v___x_3663_ = v___x_3660_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3664_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
                    v___x_3663_ = v_reuseFailAlloc_3664_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg___lam__0(
    mut v_ctx_3673_: *mut leanh::LeanObject,
    mut v_builtin_3674_: u8,
    mut v_force_3675_: u8,
    mut v_x_3676_: *mut leanh::LeanObject,
    mut v_b_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
    mut v___y_3681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3683_ = l_Lean_ParserCompiler_compileParserExpr___redArg(
        v_ctx_3673_,
        v_builtin_3674_,
        v_force_3675_,
        v_b_3677_,
        v___y_3678_,
        v___y_3679_,
        v___y_3680_,
        v___y_3681_,
    );
    return v___x_3683_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg___boxed(
    mut v_upperBound_3684_: *mut leanh::LeanObject,
    mut v_params_3685_: *mut leanh::LeanObject,
    mut v___x_3686_: *mut leanh::LeanObject,
    mut v_ctx_3687_: *mut leanh::LeanObject,
    mut v_builtin_3688_: *mut leanh::LeanObject,
    mut v_force_3689_: *mut leanh::LeanObject,
    mut v_a_3690_: *mut leanh::LeanObject,
    mut v_b_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
    mut v___y_3695_: *mut leanh::LeanObject,
    mut v___y_3696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_boxed_3697_: u8 = 0;
    let mut v_force_boxed_3698_: u8 = 0;
    let mut v_res_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3697_ = (leanh::lean_unbox(v_builtin_3688_) as u8);
    v_force_boxed_3698_ = (leanh::lean_unbox(v_force_3689_) as u8);
    v_res_3699_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_3684_, v_params_3685_, v___x_3686_, v_ctx_3687_, v_builtin_boxed_3697_, v_force_boxed_3698_, v_a_3690_, v_b_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
    leanh::lean_dec(v___y_3695_);
    leanh::lean_dec_ref(v___y_3694_);
    leanh::lean_dec(v___y_3693_);
    leanh::lean_dec_ref(v___y_3692_);
    leanh::lean_dec_ref(v___x_3686_);
    leanh::lean_dec_ref(v_params_3685_);
    leanh::lean_dec(v_upperBound_3684_);
    return v_res_3699_;
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___redArg___boxed(
    mut v_ctx_3700_: *mut leanh::LeanObject,
    mut v_builtin_3701_: *mut leanh::LeanObject,
    mut v_force_3702_: *mut leanh::LeanObject,
    mut v_e_3703_: *mut leanh::LeanObject,
    mut v_a_3704_: *mut leanh::LeanObject,
    mut v_a_3705_: *mut leanh::LeanObject,
    mut v_a_3706_: *mut leanh::LeanObject,
    mut v_a_3707_: *mut leanh::LeanObject,
    mut v_a_3708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_boxed_3709_: u8 = 0;
    let mut v_force_boxed_3710_: u8 = 0;
    let mut v_res_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3709_ = (leanh::lean_unbox(v_builtin_3701_) as u8);
    v_force_boxed_3710_ = (leanh::lean_unbox(v_force_3702_) as u8);
    v_res_3711_ = l_Lean_ParserCompiler_compileParserExpr___redArg(
        v_ctx_3700_,
        v_builtin_boxed_3709_,
        v_force_boxed_3710_,
        v_e_3703_,
        v_a_3704_,
        v_a_3705_,
        v_a_3706_,
        v_a_3707_,
    );
    leanh::lean_dec(v_a_3707_);
    leanh::lean_dec_ref(v_a_3706_);
    leanh::lean_dec(v_a_3705_);
    leanh::lean_dec_ref(v_a_3704_);
    return v_res_3711_;
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr(
    mut v_00_u03b1_3712_: *mut leanh::LeanObject,
    mut v_ctx_3713_: *mut leanh::LeanObject,
    mut v_builtin_3714_: u8,
    mut v_force_3715_: u8,
    mut v_e_3716_: *mut leanh::LeanObject,
    mut v_a_3717_: *mut leanh::LeanObject,
    mut v_a_3718_: *mut leanh::LeanObject,
    mut v_a_3719_: *mut leanh::LeanObject,
    mut v_a_3720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3722_ = l_Lean_ParserCompiler_compileParserExpr___redArg(
        v_ctx_3713_,
        v_builtin_3714_,
        v_force_3715_,
        v_e_3716_,
        v_a_3717_,
        v_a_3718_,
        v_a_3719_,
        v_a_3720_,
    );
    return v___x_3722_;
}
pub unsafe fn l_Lean_ParserCompiler_compileParserExpr___boxed(
    mut v_00_u03b1_3723_: *mut leanh::LeanObject,
    mut v_ctx_3724_: *mut leanh::LeanObject,
    mut v_builtin_3725_: *mut leanh::LeanObject,
    mut v_force_3726_: *mut leanh::LeanObject,
    mut v_e_3727_: *mut leanh::LeanObject,
    mut v_a_3728_: *mut leanh::LeanObject,
    mut v_a_3729_: *mut leanh::LeanObject,
    mut v_a_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v_a_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_boxed_3733_: u8 = 0;
    let mut v_force_boxed_3734_: u8 = 0;
    let mut v_res_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3733_ = (leanh::lean_unbox(v_builtin_3725_) as u8);
    v_force_boxed_3734_ = (leanh::lean_unbox(v_force_3726_) as u8);
    v_res_3735_ = l_Lean_ParserCompiler_compileParserExpr(
        v_00_u03b1_3723_,
        v_ctx_3724_,
        v_builtin_boxed_3733_,
        v_force_boxed_3734_,
        v_e_3727_,
        v_a_3728_,
        v_a_3729_,
        v_a_3730_,
        v_a_3731_,
    );
    leanh::lean_dec(v_a_3731_);
    leanh::lean_dec_ref(v_a_3730_);
    leanh::lean_dec(v_a_3729_);
    leanh::lean_dec_ref(v_a_3728_);
    return v_res_3735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(
    mut v_00_u03b1_3736_: *mut leanh::LeanObject,
    mut v_ctx_3737_: *mut leanh::LeanObject,
    mut v_as_3738_: *mut leanh::LeanObject,
    mut v_i_3739_: usize,
    mut v_stop_3740_: usize,
    mut v_b_3741_: *mut leanh::LeanObject,
    mut v___y_3742_: *mut leanh::LeanObject,
    mut v___y_3743_: *mut leanh::LeanObject,
    mut v___y_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___redArg(v_ctx_3737_, v_as_3738_, v_i_3739_, v_stop_3740_, v_b_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
    return v___x_3747_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0___boxed(
    mut v_00_u03b1_3748_: *mut leanh::LeanObject,
    mut v_ctx_3749_: *mut leanh::LeanObject,
    mut v_as_3750_: *mut leanh::LeanObject,
    mut v_i_3751_: *mut leanh::LeanObject,
    mut v_stop_3752_: *mut leanh::LeanObject,
    mut v_b_3753_: *mut leanh::LeanObject,
    mut v___y_3754_: *mut leanh::LeanObject,
    mut v___y_3755_: *mut leanh::LeanObject,
    mut v___y_3756_: *mut leanh::LeanObject,
    mut v___y_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3759_: usize = 0;
    let mut v_stop_boxed_3760_: usize = 0;
    let mut v_res_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3759_ = leanh::lean_unbox_usize(v_i_3751_);
    leanh::lean_dec(v_i_3751_);
    v_stop_boxed_3760_ = leanh::lean_unbox_usize(v_stop_3752_);
    leanh::lean_dec(v_stop_3752_);
    v_res_3761_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_ParserCompiler_compileParserExpr_spec__0(v_00_u03b1_3748_, v_ctx_3749_, v_as_3750_, v_i_boxed_3759_, v_stop_boxed_3760_, v_b_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
    leanh::lean_dec(v___y_3757_);
    leanh::lean_dec_ref(v___y_3756_);
    leanh::lean_dec(v___y_3755_);
    leanh::lean_dec_ref(v___y_3754_);
    leanh::lean_dec_ref(v_as_3750_);
    return v_res_3761_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(
    mut v_upperBound_3762_: *mut leanh::LeanObject,
    mut v_params_3763_: *mut leanh::LeanObject,
    mut v___x_3764_: *mut leanh::LeanObject,
    mut v_00_u03b1_3765_: *mut leanh::LeanObject,
    mut v_ctx_3766_: *mut leanh::LeanObject,
    mut v_builtin_3767_: u8,
    mut v_force_3768_: u8,
    mut v_inst_3769_: *mut leanh::LeanObject,
    mut v_R_3770_: *mut leanh::LeanObject,
    mut v_a_3771_: *mut leanh::LeanObject,
    mut v_b_3772_: *mut leanh::LeanObject,
    mut v_c_3773_: *mut leanh::LeanObject,
    mut v___y_3774_: *mut leanh::LeanObject,
    mut v___y_3775_: *mut leanh::LeanObject,
    mut v___y_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___redArg(v_upperBound_3762_, v_params_3763_, v___x_3764_, v_ctx_3766_, v_builtin_3767_, v_force_3768_, v_a_3771_, v_b_3772_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
    return v___x_3779_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_upperBound_3780_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_params_3781_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_3782_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03b1_3783_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_ctx_3784_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_builtin_3785_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_force_3786_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_inst_3787_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_R_3788_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_3789_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_b_3790_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_c_3791_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_3792_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_3793_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_3794_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_3795_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3796_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_builtin_boxed_3797_: u8 = 0;
    let mut v_force_boxed_3798_: u8 = 0;
    let mut v_res_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3797_ = (leanh::lean_unbox(v_builtin_3785_) as u8);
    v_force_boxed_3798_ = (leanh::lean_unbox(v_force_3786_) as u8);
    v_res_3799_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_ParserCompiler_compileParserExpr_spec__1(
            v_upperBound_3780_,
            v_params_3781_,
            v___x_3782_,
            v_00_u03b1_3783_,
            v_ctx_3784_,
            v_builtin_boxed_3797_,
            v_force_boxed_3798_,
            v_inst_3787_,
            v_R_3788_,
            v_a_3789_,
            v_b_3790_,
            v_c_3791_,
            v___y_3792_,
            v___y_3793_,
            v___y_3794_,
            v___y_3795_,
        );
    leanh::lean_dec(v___y_3795_);
    leanh::lean_dec_ref(v___y_3794_);
    leanh::lean_dec(v___y_3793_);
    leanh::lean_dec_ref(v___y_3792_);
    leanh::lean_dec_ref(v___x_3782_);
    leanh::lean_dec_ref(v_params_3781_);
    leanh::lean_dec(v_upperBound_3780_);
    return v_res_3799_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(
    mut v_00_u03b1_3800_: *mut leanh::LeanObject,
    mut v_msg_3801_: *mut leanh::LeanObject,
    mut v___y_3802_: *mut leanh::LeanObject,
    mut v___y_3803_: *mut leanh::LeanObject,
    mut v___y_3804_: *mut leanh::LeanObject,
    mut v___y_3805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3807_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___redArg(
        v_msg_3801_,
        v___y_3802_,
        v___y_3803_,
        v___y_3804_,
        v___y_3805_,
    );
    return v___x_3807_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4___boxed(
    mut v_00_u03b1_3808_: *mut leanh::LeanObject,
    mut v_msg_3809_: *mut leanh::LeanObject,
    mut v___y_3810_: *mut leanh::LeanObject,
    mut v___y_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
    mut v___y_3813_: *mut leanh::LeanObject,
    mut v___y_3814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3815_ = l_Lean_throwError___at___00Lean_ParserCompiler_compileParserExpr_spec__4(
        v_00_u03b1_3808_,
        v_msg_3809_,
        v___y_3810_,
        v___y_3811_,
        v___y_3812_,
        v___y_3813_,
    );
    leanh::lean_dec(v___y_3813_);
    leanh::lean_dec_ref(v___y_3812_);
    leanh::lean_dec(v___y_3811_);
    leanh::lean_dec_ref(v___y_3810_);
    return v_res_3815_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(
    mut v_00_u03b1_3816_: *mut leanh::LeanObject,
    mut v_constName_3817_: *mut leanh::LeanObject,
    mut v___y_3818_: *mut leanh::LeanObject,
    mut v___y_3819_: *mut leanh::LeanObject,
    mut v___y_3820_: *mut leanh::LeanObject,
    mut v___y_3821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___redArg(v_constName_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
    return v___x_3823_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3___boxed(
    mut v_00_u03b1_3824_: *mut leanh::LeanObject,
    mut v_constName_3825_: *mut leanh::LeanObject,
    mut v___y_3826_: *mut leanh::LeanObject,
    mut v___y_3827_: *mut leanh::LeanObject,
    mut v___y_3828_: *mut leanh::LeanObject,
    mut v___y_3829_: *mut leanh::LeanObject,
    mut v___y_3830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3831_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3(v_00_u03b1_3824_, v_constName_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
    leanh::lean_dec(v___y_3829_);
    leanh::lean_dec_ref(v___y_3828_);
    leanh::lean_dec(v___y_3827_);
    leanh::lean_dec_ref(v___y_3826_);
    return v_res_3831_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(
    mut v_00_u03b1_3832_: *mut leanh::LeanObject,
    mut v_ref_3833_: *mut leanh::LeanObject,
    mut v_constName_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
    mut v___y_3837_: *mut leanh::LeanObject,
    mut v___y_3838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3840_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg(v_ref_3833_, v_constName_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
    return v___x_3840_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___boxed(
    mut v_00_u03b1_3841_: *mut leanh::LeanObject,
    mut v_ref_3842_: *mut leanh::LeanObject,
    mut v_constName_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
    mut v___y_3845_: *mut leanh::LeanObject,
    mut v___y_3846_: *mut leanh::LeanObject,
    mut v___y_3847_: *mut leanh::LeanObject,
    mut v___y_3848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3849_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4(v_00_u03b1_3841_, v_ref_3842_, v_constName_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
    leanh::lean_dec(v___y_3847_);
    leanh::lean_dec_ref(v___y_3846_);
    leanh::lean_dec(v___y_3845_);
    leanh::lean_dec_ref(v___y_3844_);
    leanh::lean_dec(v_ref_3842_);
    return v_res_3849_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(
    mut v_00_u03b1_3850_: *mut leanh::LeanObject,
    mut v_ref_3851_: *mut leanh::LeanObject,
    mut v_msg_3852_: *mut leanh::LeanObject,
    mut v_declHint_3853_: *mut leanh::LeanObject,
    mut v___y_3854_: *mut leanh::LeanObject,
    mut v___y_3855_: *mut leanh::LeanObject,
    mut v___y_3856_: *mut leanh::LeanObject,
    mut v___y_3857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3859_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___redArg(v_ref_3851_, v_msg_3852_, v_declHint_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
    return v___x_3859_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7___boxed(
    mut v_00_u03b1_3860_: *mut leanh::LeanObject,
    mut v_ref_3861_: *mut leanh::LeanObject,
    mut v_msg_3862_: *mut leanh::LeanObject,
    mut v_declHint_3863_: *mut leanh::LeanObject,
    mut v___y_3864_: *mut leanh::LeanObject,
    mut v___y_3865_: *mut leanh::LeanObject,
    mut v___y_3866_: *mut leanh::LeanObject,
    mut v___y_3867_: *mut leanh::LeanObject,
    mut v___y_3868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7(v_00_u03b1_3860_, v_ref_3861_, v_msg_3862_, v_declHint_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
    leanh::lean_dec(v___y_3867_);
    leanh::lean_dec_ref(v___y_3866_);
    leanh::lean_dec(v___y_3865_);
    leanh::lean_dec_ref(v___y_3864_);
    leanh::lean_dec(v_ref_3861_);
    return v_res_3869_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(
    mut v_msg_3870_: *mut leanh::LeanObject,
    mut v_declHint_3871_: *mut leanh::LeanObject,
    mut v___y_3872_: *mut leanh::LeanObject,
    mut v___y_3873_: *mut leanh::LeanObject,
    mut v___y_3874_: *mut leanh::LeanObject,
    mut v___y_3875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3877_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3870_, v_declHint_3871_, v___y_3875_);
    return v___x_3877_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(
    mut v_msg_3878_: *mut leanh::LeanObject,
    mut v_declHint_3879_: *mut leanh::LeanObject,
    mut v___y_3880_: *mut leanh::LeanObject,
    mut v___y_3881_: *mut leanh::LeanObject,
    mut v___y_3882_: *mut leanh::LeanObject,
    mut v___y_3883_: *mut leanh::LeanObject,
    mut v___y_3884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3885_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_3878_, v_declHint_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
    leanh::lean_dec(v___y_3883_);
    leanh::lean_dec_ref(v___y_3882_);
    leanh::lean_dec(v___y_3881_);
    leanh::lean_dec_ref(v___y_3880_);
    return v_res_3885_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(
    mut v_00_u03b1_3886_: *mut leanh::LeanObject,
    mut v_ref_3887_: *mut leanh::LeanObject,
    mut v_msg_3888_: *mut leanh::LeanObject,
    mut v___y_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
    mut v___y_3891_: *mut leanh::LeanObject,
    mut v___y_3892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3894_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3887_, v_msg_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
    return v___x_3894_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9___boxed(
    mut v_00_u03b1_3895_: *mut leanh::LeanObject,
    mut v_ref_3896_: *mut leanh::LeanObject,
    mut v_msg_3897_: *mut leanh::LeanObject,
    mut v___y_3898_: *mut leanh::LeanObject,
    mut v___y_3899_: *mut leanh::LeanObject,
    mut v___y_3900_: *mut leanh::LeanObject,
    mut v___y_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_3895_, v_ref_3896_, v_msg_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
    leanh::lean_dec(v___y_3901_);
    leanh::lean_dec_ref(v___y_3900_);
    leanh::lean_dec(v___y_3899_);
    leanh::lean_dec_ref(v___y_3898_);
    leanh::lean_dec(v_ref_3896_);
    return v_res_3903_;
}
pub unsafe fn l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(
    mut v_ctx_3904_: *mut leanh::LeanObject,
    mut v_builtin_3905_: u8,
    mut v_x_3906_: *mut leanh::LeanObject,
    mut v_a_3907_: *mut leanh::LeanObject,
    mut v_a_3908_: *mut leanh::LeanObject,
    mut v_a_3909_: *mut leanh::LeanObject,
    mut v_a_3910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_psep_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2081_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2082_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_unused_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3948_: u8 = 0;
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3952_: u8 = 0;
    let mut v_p_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_psep_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_psep_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3906_) {
                1 => {
                    v_p_3921_ = leanh::lean_ctor_get(v_x_3906_, 1);
                    leanh::lean_inc_ref(v_p_3921_);
                    leanh::lean_dec_ref_known(v_x_3906_, 2);
                    v_x_3906_ = v_p_3921_;
                    state = 0;
                    continue;
                }
                2 => {
                    v_p_u2081_3923_ = leanh::lean_ctor_get(v_x_3906_, 1);
                    leanh::lean_inc_ref(v_p_u2081_3923_);
                    v_p_u2082_3924_ = leanh::lean_ctor_get(v_x_3906_, 2);
                    leanh::lean_inc_ref(v_p_u2082_3924_);
                    leanh::lean_dec_ref_known(v_x_3906_, 3);
                    leanh::lean_inc_ref(v_ctx_3904_);
                    v___x_3925_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(
                        v_ctx_3904_,
                        v_builtin_3905_,
                        v_p_u2081_3923_,
                        v_a_3907_,
                        v_a_3908_,
                        v_a_3909_,
                        v_a_3910_,
                    );
                    if leanh::lean_obj_tag(v___x_3925_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3925_, 1);
                        v_x_3906_ = v_p_u2082_3924_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_p_u2082_3924_);
                        leanh::lean_dec_ref(v_ctx_3904_);
                        return v___x_3925_;
                    }
                }
                3 => {
                    v_p_3927_ = leanh::lean_ctor_get(v_x_3906_, 2);
                    leanh::lean_inc_ref(v_p_3927_);
                    leanh::lean_dec_ref_known(v_x_3906_, 3);
                    v_x_3906_ = v_p_3927_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_p_3929_ = leanh::lean_ctor_get(v_x_3906_, 3);
                    leanh::lean_inc_ref(v_p_3929_);
                    leanh::lean_dec_ref_known(v_x_3906_, 4);
                    v_x_3906_ = v_p_3929_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_declName_3931_ = leanh::lean_ctor_get(v_x_3906_, 0);
                    leanh::lean_inc(v_declName_3931_);
                    leanh::lean_dec_ref_known(v_x_3906_, 1);
                    v___x_3932_ = 0;
                    v___x_3933_ = leanh::lean_box(0);
                    v___x_3934_ = l_Lean_mkConst(v_declName_3931_, v___x_3933_);
                    v___x_3935_ = l_Lean_ParserCompiler_compileParserExpr___redArg(
                        v_ctx_3904_,
                        v_builtin_3905_,
                        v___x_3932_,
                        v___x_3934_,
                        v_a_3907_,
                        v_a_3908_,
                        v_a_3909_,
                        v_a_3910_,
                    );
                    if leanh::lean_obj_tag(v___x_3935_) == 0 {
                        v_isSharedCheck_3943_ =
                            (!leanh::lean_is_exclusive(v___x_3935_)) as u8;
                        if v_isSharedCheck_3943_ == 0 {
                            v_unused_3944_ = leanh::lean_ctor_get(v___x_3935_, 0);
                            leanh::lean_dec(v_unused_3944_);
                            v___x_3937_ = v___x_3935_;
                            v_isShared_3938_ = v_isSharedCheck_3943_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3935_);
                            v___x_3937_ = leanh::lean_box(0);
                            v_isShared_3938_ = v_isSharedCheck_3943_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3945_ = leanh::lean_ctor_get(v___x_3935_, 0);
                        v_isSharedCheck_3952_ =
                            (!leanh::lean_is_exclusive(v___x_3935_)) as u8;
                        if v_isSharedCheck_3952_ == 0 {
                            v___x_3947_ = v___x_3935_;
                            v_isShared_3948_ = v_isSharedCheck_3952_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3945_);
                            leanh::lean_dec(v___x_3935_);
                            v___x_3947_ = leanh::lean_box(0);
                            v_isShared_3948_ = v_isSharedCheck_3952_;
                            state = 4;
                            continue;
                        }
                    }
                }
                9 => {
                    v_p_3953_ = leanh::lean_ctor_get(v_x_3906_, 2);
                    leanh::lean_inc_ref(v_p_3953_);
                    leanh::lean_dec_ref_known(v_x_3906_, 3);
                    v_x_3906_ = v_p_3953_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_p_3955_ = leanh::lean_ctor_get(v_x_3906_, 0);
                    leanh::lean_inc_ref(v_p_3955_);
                    v_psep_3956_ = leanh::lean_ctor_get(v_x_3906_, 2);
                    leanh::lean_inc_ref(v_psep_3956_);
                    leanh::lean_dec_ref_known(v_x_3906_, 3);
                    v_p_3913_ = v_p_3955_;
                    v_psep_3914_ = v_psep_3956_;
                    v___y_3915_ = v_a_3907_;
                    v___y_3916_ = v_a_3908_;
                    v___y_3917_ = v_a_3909_;
                    v___y_3918_ = v_a_3910_;
                    state = 1;
                    continue;
                }
                11 => {
                    v_p_3957_ = leanh::lean_ctor_get(v_x_3906_, 0);
                    leanh::lean_inc_ref(v_p_3957_);
                    v_psep_3958_ = leanh::lean_ctor_get(v_x_3906_, 2);
                    leanh::lean_inc_ref(v_psep_3958_);
                    leanh::lean_dec_ref_known(v_x_3906_, 3);
                    v_p_3913_ = v_p_3957_;
                    v_psep_3914_ = v_psep_3958_;
                    v___y_3915_ = v_a_3907_;
                    v___y_3916_ = v_a_3908_;
                    v___y_3917_ = v_a_3909_;
                    v___y_3918_ = v_a_3910_;
                    state = 1;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_x_3906_);
                    leanh::lean_dec_ref(v_ctx_3904_);
                    v___x_3959_ = leanh::lean_box(0);
                    v___x_3960_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3960_, 0, v___x_3959_);
                    return v___x_3960_;
                }
            },
            1 => {
                leanh::lean_inc_ref(v_ctx_3904_);
                v___x_3919_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(
                    v_ctx_3904_,
                    v_builtin_3905_,
                    v_p_3913_,
                    v___y_3915_,
                    v___y_3916_,
                    v___y_3917_,
                    v___y_3918_,
                );
                if leanh::lean_obj_tag(v___x_3919_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3919_, 1);
                    v_x_3906_ = v_psep_3914_;
                    v_a_3907_ = v___y_3915_;
                    v_a_3908_ = v___y_3916_;
                    v_a_3909_ = v___y_3917_;
                    v_a_3910_ = v___y_3918_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_psep_3914_);
                    leanh::lean_dec_ref(v_ctx_3904_);
                    return v___x_3919_;
                }
            }
            2 => {
                v___x_3939_ = leanh::lean_box(0);
                if v_isShared_3938_ == 0 {
                    leanh::lean_ctor_set(v___x_3937_, 0, v___x_3939_);
                    v___x_3941_ = v___x_3937_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
                    v___x_3941_ = v_reuseFailAlloc_3942_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3941_;
            }
            4 => {
                if v_isShared_3948_ == 0 {
                    v___x_3950_ = v___x_3947_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3951_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
                    v___x_3950_ = v_reuseFailAlloc_3951_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_compileEmbeddedParsers___redArg___boxed(
    mut v_ctx_3961_: *mut leanh::LeanObject,
    mut v_builtin_3962_: *mut leanh::LeanObject,
    mut v_x_3963_: *mut leanh::LeanObject,
    mut v_a_3964_: *mut leanh::LeanObject,
    mut v_a_3965_: *mut leanh::LeanObject,
    mut v_a_3966_: *mut leanh::LeanObject,
    mut v_a_3967_: *mut leanh::LeanObject,
    mut v_a_3968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_boxed_3969_: u8 = 0;
    let mut v_res_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3969_ = (leanh::lean_unbox(v_builtin_3962_) as u8);
    v_res_3970_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(
        v_ctx_3961_,
        v_builtin_boxed_3969_,
        v_x_3963_,
        v_a_3964_,
        v_a_3965_,
        v_a_3966_,
        v_a_3967_,
    );
    leanh::lean_dec(v_a_3967_);
    leanh::lean_dec_ref(v_a_3966_);
    leanh::lean_dec(v_a_3965_);
    leanh::lean_dec_ref(v_a_3964_);
    return v_res_3970_;
}
pub unsafe fn l_Lean_ParserCompiler_compileEmbeddedParsers(
    mut v_00_u03b1_3971_: *mut leanh::LeanObject,
    mut v_ctx_3972_: *mut leanh::LeanObject,
    mut v_builtin_3973_: u8,
    mut v_x_3974_: *mut leanh::LeanObject,
    mut v_a_3975_: *mut leanh::LeanObject,
    mut v_a_3976_: *mut leanh::LeanObject,
    mut v_a_3977_: *mut leanh::LeanObject,
    mut v_a_3978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3980_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(
        v_ctx_3972_,
        v_builtin_3973_,
        v_x_3974_,
        v_a_3975_,
        v_a_3976_,
        v_a_3977_,
        v_a_3978_,
    );
    return v___x_3980_;
}
pub unsafe fn l_Lean_ParserCompiler_compileEmbeddedParsers___boxed(
    mut v_00_u03b1_3981_: *mut leanh::LeanObject,
    mut v_ctx_3982_: *mut leanh::LeanObject,
    mut v_builtin_3983_: *mut leanh::LeanObject,
    mut v_x_3984_: *mut leanh::LeanObject,
    mut v_a_3985_: *mut leanh::LeanObject,
    mut v_a_3986_: *mut leanh::LeanObject,
    mut v_a_3987_: *mut leanh::LeanObject,
    mut v_a_3988_: *mut leanh::LeanObject,
    mut v_a_3989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_boxed_3990_: u8 = 0;
    let mut v_res_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3990_ = (leanh::lean_unbox(v_builtin_3983_) as u8);
    v_res_3991_ = l_Lean_ParserCompiler_compileEmbeddedParsers(
        v_00_u03b1_3981_,
        v_ctx_3982_,
        v_builtin_boxed_3990_,
        v_x_3984_,
        v_a_3985_,
        v_a_3986_,
        v_a_3987_,
        v_a_3988_,
    );
    leanh::lean_dec(v_a_3988_);
    leanh::lean_dec_ref(v_a_3987_);
    leanh::lean_dec(v_a_3986_);
    leanh::lean_dec_ref(v_a_3985_);
    return v_res_3991_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3992_ = leanh::lean_box(0);
    v___x_3993_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_3994_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3994_, 0, v___x_3993_);
    leanh::lean_ctor_set(v___x_3994_, 1, v___x_3992_);
    return v___x_3994_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3996_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___closed__0);
    v___x_3997_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3997_, 0, v___x_3996_);
    return v___x_3997_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg___boxed(
    mut v___y_3998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3999_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
    return v_res_3999_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(
    mut v_msgData_4000_: *mut leanh::LeanObject,
    mut v___y_4001_: *mut leanh::LeanObject,
    mut v___y_4002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4004_ = lean_st_ref_get(v___y_4002_);
    v_env_4005_ = leanh::lean_ctor_get(v___x_4004_, 0);
    leanh::lean_inc_ref(v_env_4005_);
    leanh::lean_dec(v___x_4004_);
    v_options_4006_ = leanh::lean_ctor_get(v___y_4001_, 2);
    v___x_4007_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
    v___x_4008_ = leanh::lean_unsigned_to_nat(32);
    v___x_4009_ = lean_mk_empty_array_with_capacity(v___x_4008_);
    leanh::lean_dec_ref(v___x_4009_);
    v___x_4010_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
    leanh::lean_inc_ref(v_options_4006_);
    v___x_4011_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4011_, 0, v_env_4005_);
    leanh::lean_ctor_set(v___x_4011_, 1, v___x_4007_);
    leanh::lean_ctor_set(v___x_4011_, 2, v___x_4010_);
    leanh::lean_ctor_set(v___x_4011_, 3, v_options_4006_);
    v___x_4012_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4012_, 0, v___x_4011_);
    leanh::lean_ctor_set(v___x_4012_, 1, v_msgData_4000_);
    v___x_4013_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4013_, 0, v___x_4012_);
    return v___x_4013_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9___boxed(
    mut v_msgData_4014_: *mut leanh::LeanObject,
    mut v___y_4015_: *mut leanh::LeanObject,
    mut v___y_4016_: *mut leanh::LeanObject,
    mut v___y_4017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4018_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msgData_4014_, v___y_4015_, v___y_4016_);
    leanh::lean_dec(v___y_4016_);
    leanh::lean_dec_ref(v___y_4015_);
    return v_res_4018_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(
    mut v_msg_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4028_: u8 = 0;
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4023_ = leanh::lean_ctor_get(v___y_4020_, 5);
                v___x_4024_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4_spec__9(v_msg_4019_, v___y_4020_, v___y_4021_);
                v_a_4025_ = leanh::lean_ctor_get(v___x_4024_, 0);
                v_isSharedCheck_4033_ = (!leanh::lean_is_exclusive(v___x_4024_)) as u8;
                if v_isSharedCheck_4033_ == 0 {
                    v___x_4027_ = v___x_4024_;
                    v_isShared_4028_ = v_isSharedCheck_4033_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4025_);
                    leanh::lean_dec(v___x_4024_);
                    v___x_4027_ = leanh::lean_box(0);
                    v_isShared_4028_ = v_isSharedCheck_4033_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4023_);
                v___x_4029_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4029_, 0, v_ref_4023_);
                leanh::lean_ctor_set(v___x_4029_, 1, v_a_4025_);
                if v_isShared_4028_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4027_, 1);
                    leanh::lean_ctor_set(v___x_4027_, 0, v___x_4029_);
                    v___x_4031_ = v___x_4027_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4032_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4029_);
                    v___x_4031_ = v_reuseFailAlloc_4032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_msg_4034_: *mut leanh::LeanObject,
    mut v___y_4035_: *mut leanh::LeanObject,
    mut v___y_4036_: *mut leanh::LeanObject,
    mut v___y_4037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4038_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_4034_, v___y_4035_, v___y_4036_);
    leanh::lean_dec(v___y_4036_);
    leanh::lean_dec_ref(v___y_4035_);
    return v_res_4038_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(
    mut v_x_4039_: *mut leanh::LeanObject,
    mut v___y_4040_: *mut leanh::LeanObject,
    mut v___y_4041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4053_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4039_) == 0 {
                    v_a_4043_ = leanh::lean_ctor_get(v_x_4039_, 0);
                    leanh::lean_inc(v_a_4043_);
                    leanh::lean_dec_ref_known(v_x_4039_, 1);
                    v___x_4044_ = l_Lean_stringToMessageData(v_a_4043_);
                    v___x_4045_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v___x_4044_, v___y_4040_, v___y_4041_);
                    return v___x_4045_;
                } else {
                    v_a_4046_ = leanh::lean_ctor_get(v_x_4039_, 0);
                    v_isSharedCheck_4053_ = (!leanh::lean_is_exclusive(v_x_4039_)) as u8;
                    if v_isSharedCheck_4053_ == 0 {
                        v___x_4048_ = v_x_4039_;
                        v_isShared_4049_ = v_isSharedCheck_4053_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4046_);
                        leanh::lean_dec(v_x_4039_);
                        v___x_4048_ = leanh::lean_box(0);
                        v_isShared_4049_ = v_isSharedCheck_4053_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4049_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4048_, 0);
                    v___x_4051_ = v___x_4048_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4052_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
                    v___x_4051_ = v_reuseFailAlloc_4052_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg___boxed(
    mut v_x_4054_: *mut leanh::LeanObject,
    mut v___y_4055_: *mut leanh::LeanObject,
    mut v___y_4056_: *mut leanh::LeanObject,
    mut v___y_4057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4058_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_4054_, v___y_4055_, v___y_4056_);
    leanh::lean_dec(v___y_4056_);
    leanh::lean_dec_ref(v___y_4055_);
    return v_res_4058_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(
    mut v_typeName_4059_: *mut leanh::LeanObject,
    mut v_constName_4060_: *mut leanh::LeanObject,
    mut v___y_4061_: *mut leanh::LeanObject,
    mut v___y_4062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: u8 = 0;
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4064_ = lean_st_ref_get(v___y_4062_);
                v_env_4065_ = leanh::lean_ctor_get(v___x_4064_, 0);
                leanh::lean_inc_ref(v_env_4065_);
                leanh::lean_dec(v___x_4064_);
                leanh::lean_inc(v_constName_4060_);
                v___x_4066_ = lean_has_compile_error(v_env_4065_, v_constName_4060_);
                if v___x_4066_ == 0 {
                    v___x_4067_ = lean_st_ref_get(v___y_4062_);
                    v_env_4068_ = leanh::lean_ctor_get(v___x_4067_, 0);
                    leanh::lean_inc_ref(v_env_4068_);
                    leanh::lean_dec(v___x_4067_);
                    v_options_4069_ = leanh::lean_ctor_get(v___y_4061_, 2);
                    v___x_4070_ = l_Lean_Environment_evalConstCheck___redArg(
                        v_env_4068_,
                        v_options_4069_,
                        v_typeName_4059_,
                        v_constName_4060_,
                    );
                    v___x_4071_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_4070_, v___y_4061_, v___y_4062_);
                    return v___x_4071_;
                } else {
                    v___x_4072_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
                    if leanh::lean_obj_tag(v___x_4072_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4072_, 1);
                        v___x_4073_ = lean_st_ref_get(v___y_4062_);
                        v_env_4074_ = leanh::lean_ctor_get(v___x_4073_, 0);
                        leanh::lean_inc_ref(v_env_4074_);
                        leanh::lean_dec(v___x_4073_);
                        v_options_4075_ = leanh::lean_ctor_get(v___y_4061_, 2);
                        v___x_4076_ = l_Lean_Environment_evalConstCheck___redArg(
                            v_env_4074_,
                            v_options_4075_,
                            v_typeName_4059_,
                            v_constName_4060_,
                        );
                        v___x_4077_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v___x_4076_, v___y_4061_, v___y_4062_);
                        return v___x_4077_;
                    } else {
                        leanh::lean_dec(v_constName_4060_);
                        leanh::lean_dec(v_typeName_4059_);
                        v_a_4078_ = leanh::lean_ctor_get(v___x_4072_, 0);
                        v_isSharedCheck_4085_ =
                            (!leanh::lean_is_exclusive(v___x_4072_)) as u8;
                        if v_isSharedCheck_4085_ == 0 {
                            v___x_4080_ = v___x_4072_;
                            v_isShared_4081_ = v_isSharedCheck_4085_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4078_);
                            leanh::lean_dec(v___x_4072_);
                            v___x_4080_ = leanh::lean_box(0);
                            v_isShared_4081_ = v_isSharedCheck_4085_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4081_ == 0 {
                    v___x_4083_ = v___x_4080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
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
pub unsafe fn l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg___boxed(
    mut v_typeName_4086_: *mut leanh::LeanObject,
    mut v_constName_4087_: *mut leanh::LeanObject,
    mut v___y_4088_: *mut leanh::LeanObject,
    mut v___y_4089_: *mut leanh::LeanObject,
    mut v___y_4090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4091_ =
        l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(
            v_typeName_4086_,
            v_constName_4087_,
            v___y_4088_,
            v___y_4089_,
        );
    leanh::lean_dec(v___y_4089_);
    leanh::lean_dec_ref(v___y_4088_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(
    mut v_ref_4092_: *mut leanh::LeanObject,
    mut v_msg_4093_: *mut leanh::LeanObject,
    mut v___y_4094_: *mut leanh::LeanObject,
    mut v___y_4095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4109_: u8 = 0;
    let mut v_cancelTk_x3f_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4111_: u8 = 0;
    let mut v_inheritedTraceOptions_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4097_ = leanh::lean_ctor_get(v___y_4094_, 0);
    v_fileMap_4098_ = leanh::lean_ctor_get(v___y_4094_, 1);
    v_options_4099_ = leanh::lean_ctor_get(v___y_4094_, 2);
    v_currRecDepth_4100_ = leanh::lean_ctor_get(v___y_4094_, 3);
    v_maxRecDepth_4101_ = leanh::lean_ctor_get(v___y_4094_, 4);
    v_ref_4102_ = leanh::lean_ctor_get(v___y_4094_, 5);
    v_currNamespace_4103_ = leanh::lean_ctor_get(v___y_4094_, 6);
    v_openDecls_4104_ = leanh::lean_ctor_get(v___y_4094_, 7);
    v_initHeartbeats_4105_ = leanh::lean_ctor_get(v___y_4094_, 8);
    v_maxHeartbeats_4106_ = leanh::lean_ctor_get(v___y_4094_, 9);
    v_quotContext_4107_ = leanh::lean_ctor_get(v___y_4094_, 10);
    v_currMacroScope_4108_ = leanh::lean_ctor_get(v___y_4094_, 11);
    v_diag_4109_ = leanh::lean_ctor_get_uint8(
        v___y_4094_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4110_ = leanh::lean_ctor_get(v___y_4094_, 12);
    v_suppressElabErrors_4111_ = leanh::lean_ctor_get_uint8(
        v___y_4094_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4112_ = leanh::lean_ctor_get(v___y_4094_, 13);
    v_ref_4113_ = l_Lean_replaceRef(v_ref_4092_, v_ref_4102_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_4112_);
    leanh::lean_inc(v_cancelTk_x3f_4110_);
    leanh::lean_inc(v_currMacroScope_4108_);
    leanh::lean_inc(v_quotContext_4107_);
    leanh::lean_inc(v_maxHeartbeats_4106_);
    leanh::lean_inc(v_initHeartbeats_4105_);
    leanh::lean_inc(v_openDecls_4104_);
    leanh::lean_inc(v_currNamespace_4103_);
    leanh::lean_inc(v_maxRecDepth_4101_);
    leanh::lean_inc(v_currRecDepth_4100_);
    leanh::lean_inc_ref(v_options_4099_);
    leanh::lean_inc_ref(v_fileMap_4098_);
    leanh::lean_inc_ref(v_fileName_4097_);
    v___x_4114_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_4114_, 0, v_fileName_4097_);
    leanh::lean_ctor_set(v___x_4114_, 1, v_fileMap_4098_);
    leanh::lean_ctor_set(v___x_4114_, 2, v_options_4099_);
    leanh::lean_ctor_set(v___x_4114_, 3, v_currRecDepth_4100_);
    leanh::lean_ctor_set(v___x_4114_, 4, v_maxRecDepth_4101_);
    leanh::lean_ctor_set(v___x_4114_, 5, v_ref_4113_);
    leanh::lean_ctor_set(v___x_4114_, 6, v_currNamespace_4103_);
    leanh::lean_ctor_set(v___x_4114_, 7, v_openDecls_4104_);
    leanh::lean_ctor_set(v___x_4114_, 8, v_initHeartbeats_4105_);
    leanh::lean_ctor_set(v___x_4114_, 9, v_maxHeartbeats_4106_);
    leanh::lean_ctor_set(v___x_4114_, 10, v_quotContext_4107_);
    leanh::lean_ctor_set(v___x_4114_, 11, v_currMacroScope_4108_);
    leanh::lean_ctor_set(v___x_4114_, 12, v_cancelTk_x3f_4110_);
    leanh::lean_ctor_set(v___x_4114_, 13, v_inheritedTraceOptions_4112_);
    leanh::lean_ctor_set_uint8(
        v___x_4114_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_4109_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4114_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4111_,
    );
    v___x_4115_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_4093_, v___x_4114_, v___y_4095_);
    leanh::lean_dec_ref_known(v___x_4114_, 14);
    return v___x_4115_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg___boxed(
    mut v_ref_4116_: *mut leanh::LeanObject,
    mut v_msg_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
    mut v___y_4120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4121_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_4116_, v_msg_4117_, v___y_4118_, v___y_4119_);
    leanh::lean_dec(v___y_4119_);
    leanh::lean_dec_ref(v___y_4118_);
    leanh::lean_dec(v_ref_4116_);
    return v_res_4121_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(
    mut v_msg_4122_: *mut leanh::LeanObject,
    mut v_declHint_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: u8 = 0;
    let mut v_isExporting_4129_: u8 = 0;
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: u8 = 0;
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: u8 = 0;
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4126_ = lean_st_ref_get(v___y_4124_);
                v_env_4127_ = leanh::lean_ctor_get(v___x_4126_, 0);
                leanh::lean_inc_ref(v_env_4127_);
                leanh::lean_dec(v___x_4126_);
                v___x_4128_ = l_Lean_Name_isAnonymous(v_declHint_4123_);
                if v___x_4128_ == 0 {
                    v_isExporting_4129_ = leanh::lean_ctor_get_uint8(
                        v_env_4127_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4129_ == 0 {
                        leanh::lean_dec_ref(v_env_4127_);
                        leanh::lean_dec(v_declHint_4123_);
                        v___x_4130_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4130_, 0, v_msg_4122_);
                        return v___x_4130_;
                    } else {
                        leanh::lean_inc_ref(v_env_4127_);
                        v___x_4131_ = l_Lean_Environment_setExporting(v_env_4127_, v___x_4128_);
                        leanh::lean_inc(v_declHint_4123_);
                        leanh::lean_inc_ref(v___x_4131_);
                        v___x_4132_ = l_Lean_Environment_contains(
                            v___x_4131_,
                            v_declHint_4123_,
                            v_isExporting_4129_,
                        );
                        if v___x_4132_ == 0 {
                            leanh::lean_dec_ref(v___x_4131_);
                            leanh::lean_dec_ref(v_env_4127_);
                            leanh::lean_dec(v_declHint_4123_);
                            v___x_4133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4133_, 0, v_msg_4122_);
                            return v___x_4133_;
                        } else {
                            v___x_4134_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_4135_ = leanh::lean_unsigned_to_nat(32);
                            v___x_4136_ = lean_mk_empty_array_with_capacity(v___x_4135_);
                            leanh::lean_dec_ref(v___x_4136_);
                            v___x_4137_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
                            v___x_4138_ = l_Lean_Options_empty;
                            v___x_4139_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_4139_, 0, v___x_4131_);
                            leanh::lean_ctor_set(v___x_4139_, 1, v___x_4134_);
                            leanh::lean_ctor_set(v___x_4139_, 2, v___x_4137_);
                            leanh::lean_ctor_set(v___x_4139_, 3, v___x_4138_);
                            leanh::lean_inc(v_declHint_4123_);
                            v___x_4140_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4123_, v___x_4128_);
                            v_c_4141_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_4141_, 0, v___x_4139_);
                            leanh::lean_ctor_set(v_c_4141_, 1, v___x_4140_);
                            v___x_4142_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4127_,
                                v_declHint_4123_,
                            );
                            if leanh::lean_obj_tag(v___x_4142_) == 0 {
                                leanh::lean_dec_ref(v_env_4127_);
                                leanh::lean_dec(v_declHint_4123_);
                                v___x_4143_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_4144_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4144_, 0, v___x_4143_);
                                leanh::lean_ctor_set(v___x_4144_, 1, v_c_4141_);
                                v___x_4145_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
                                v___x_4146_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4146_, 0, v___x_4144_);
                                leanh::lean_ctor_set(v___x_4146_, 1, v___x_4145_);
                                v___x_4147_ = l_Lean_MessageData_note(v___x_4146_);
                                v___x_4148_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4148_, 0, v_msg_4122_);
                                leanh::lean_ctor_set(v___x_4148_, 1, v___x_4147_);
                                v___x_4149_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4149_, 0, v___x_4148_);
                                return v___x_4149_;
                            } else {
                                v_val_4150_ = leanh::lean_ctor_get(v___x_4142_, 0);
                                v_isSharedCheck_4185_ =
                                    (!leanh::lean_is_exclusive(v___x_4142_)) as u8;
                                if v_isSharedCheck_4185_ == 0 {
                                    v___x_4152_ = v___x_4142_;
                                    v_isShared_4153_ = v_isSharedCheck_4185_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_4150_);
                                    leanh::lean_dec(v___x_4142_);
                                    v___x_4152_ = leanh::lean_box(0);
                                    v_isShared_4153_ = v_isSharedCheck_4185_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4127_);
                    leanh::lean_dec(v_declHint_4123_);
                    v___x_4186_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4186_, 0, v_msg_4122_);
                    return v___x_4186_;
                }
            }
            1 => {
                v___x_4154_ = leanh::lean_box(0);
                v___x_4155_ = l_Lean_Environment_header(v_env_4127_);
                leanh::lean_dec_ref(v_env_4127_);
                v___x_4156_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4155_);
                v_mod_4157_ = lean_array_get(v___x_4154_, v___x_4156_, v_val_4150_);
                leanh::lean_dec(v_val_4150_);
                leanh::lean_dec_ref(v___x_4156_);
                v___x_4158_ = l_Lean_isPrivateName(v_declHint_4123_);
                leanh::lean_dec(v_declHint_4123_);
                if v___x_4158_ == 0 {
                    v___x_4159_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_4160_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4160_, 0, v___x_4159_);
                    leanh::lean_ctor_set(v___x_4160_, 1, v_c_4141_);
                    v___x_4161_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_4162_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4162_, 0, v___x_4160_);
                    leanh::lean_ctor_set(v___x_4162_, 1, v___x_4161_);
                    v___x_4163_ = l_Lean_MessageData_ofName(v_mod_4157_);
                    v___x_4164_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4164_, 0, v___x_4162_);
                    leanh::lean_ctor_set(v___x_4164_, 1, v___x_4163_);
                    v___x_4165_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_4166_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4166_, 0, v___x_4164_);
                    leanh::lean_ctor_set(v___x_4166_, 1, v___x_4165_);
                    v___x_4167_ = l_Lean_MessageData_note(v___x_4166_);
                    v___x_4168_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4168_, 0, v_msg_4122_);
                    leanh::lean_ctor_set(v___x_4168_, 1, v___x_4167_);
                    if v_isShared_4153_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4152_, 0);
                        leanh::lean_ctor_set(v___x_4152_, 0, v___x_4168_);
                        v___x_4170_ = v___x_4152_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4168_);
                        v___x_4170_ = v_reuseFailAlloc_4171_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4172_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_4173_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4173_, 0, v___x_4172_);
                    leanh::lean_ctor_set(v___x_4173_, 1, v_c_4141_);
                    v___x_4174_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_4175_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4175_, 0, v___x_4173_);
                    leanh::lean_ctor_set(v___x_4175_, 1, v___x_4174_);
                    v___x_4176_ = l_Lean_MessageData_ofName(v_mod_4157_);
                    v___x_4177_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4177_, 0, v___x_4175_);
                    leanh::lean_ctor_set(v___x_4177_, 1, v___x_4176_);
                    v___x_4178_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__19);
                    v___x_4179_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4179_, 0, v___x_4177_);
                    leanh::lean_ctor_set(v___x_4179_, 1, v___x_4178_);
                    v___x_4180_ = l_Lean_MessageData_note(v___x_4179_);
                    v___x_4181_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4181_, 0, v_msg_4122_);
                    leanh::lean_ctor_set(v___x_4181_, 1, v___x_4180_);
                    if v_isShared_4153_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4152_, 0);
                        leanh::lean_ctor_set(v___x_4152_, 0, v___x_4181_);
                        v___x_4183_ = v___x_4152_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4184_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
                        v___x_4183_ = v_reuseFailAlloc_4184_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4170_;
            }
            3 => {
                return v___x_4183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg___boxed(
    mut v_msg_4187_: *mut leanh::LeanObject,
    mut v_declHint_4188_: *mut leanh::LeanObject,
    mut v___y_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4191_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_4187_, v_declHint_4188_, v___y_4189_);
    leanh::lean_dec(v___y_4189_);
    return v_res_4191_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(
    mut v_msg_4192_: *mut leanh::LeanObject,
    mut v_declHint_4193_: *mut leanh::LeanObject,
    mut v___y_4194_: *mut leanh::LeanObject,
    mut v___y_4195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4201_: u8 = 0;
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4197_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_4192_, v_declHint_4193_, v___y_4195_);
                v_a_4198_ = leanh::lean_ctor_get(v___x_4197_, 0);
                v_isSharedCheck_4207_ = (!leanh::lean_is_exclusive(v___x_4197_)) as u8;
                if v_isSharedCheck_4207_ == 0 {
                    v___x_4200_ = v___x_4197_;
                    v_isShared_4201_ = v_isSharedCheck_4207_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4198_);
                    leanh::lean_dec(v___x_4197_);
                    v___x_4200_ = leanh::lean_box(0);
                    v_isShared_4201_ = v_isSharedCheck_4207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4202_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4203_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4203_, 0, v___x_4202_);
                leanh::lean_ctor_set(v___x_4203_, 1, v_a_4198_);
                if v_isShared_4201_ == 0 {
                    leanh::lean_ctor_set(v___x_4200_, 0, v___x_4203_);
                    v___x_4205_ = v___x_4200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4206_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4203_);
                    v___x_4205_ = v_reuseFailAlloc_4206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(
    mut v_msg_4208_: *mut leanh::LeanObject,
    mut v_declHint_4209_: *mut leanh::LeanObject,
    mut v___y_4210_: *mut leanh::LeanObject,
    mut v___y_4211_: *mut leanh::LeanObject,
    mut v___y_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4213_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_4208_, v_declHint_4209_, v___y_4210_, v___y_4211_);
    leanh::lean_dec(v___y_4211_);
    leanh::lean_dec_ref(v___y_4210_);
    return v_res_4213_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(
    mut v_ref_4214_: *mut leanh::LeanObject,
    mut v_msg_4215_: *mut leanh::LeanObject,
    mut v_declHint_4216_: *mut leanh::LeanObject,
    mut v___y_4217_: *mut leanh::LeanObject,
    mut v___y_4218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4220_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_4215_, v_declHint_4216_, v___y_4217_, v___y_4218_);
    v_a_4221_ = leanh::lean_ctor_get(v___x_4220_, 0);
    leanh::lean_inc(v_a_4221_);
    leanh::lean_dec_ref(v___x_4220_);
    v___x_4222_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_4214_, v_a_4221_, v___y_4217_, v___y_4218_);
    return v___x_4222_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg___boxed(
    mut v_ref_4223_: *mut leanh::LeanObject,
    mut v_msg_4224_: *mut leanh::LeanObject,
    mut v_declHint_4225_: *mut leanh::LeanObject,
    mut v___y_4226_: *mut leanh::LeanObject,
    mut v___y_4227_: *mut leanh::LeanObject,
    mut v___y_4228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4229_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_4223_, v_msg_4224_, v_declHint_4225_, v___y_4226_, v___y_4227_);
    leanh::lean_dec(v___y_4227_);
    leanh::lean_dec_ref(v___y_4226_);
    leanh::lean_dec(v_ref_4223_);
    return v_res_4229_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(
    mut v_ref_4230_: *mut leanh::LeanObject,
    mut v_constName_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4235_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__1);
    v___x_4236_ = 0;
    leanh::lean_inc(v_constName_4231_);
    v___x_4237_ = l_Lean_MessageData_ofConstName(v_constName_4231_, v___x_4236_);
    v___x_4238_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4238_, 0, v___x_4235_);
    leanh::lean_ctor_set(v___x_4238_, 1, v___x_4237_);
    v___x_4239_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4___redArg___closed__3);
    v___x_4240_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4240_, 0, v___x_4238_);
    leanh::lean_ctor_set(v___x_4240_, 1, v___x_4239_);
    v___x_4241_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_4230_, v___x_4240_, v_constName_4231_, v___y_4232_, v___y_4233_);
    return v___x_4241_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4242_: *mut leanh::LeanObject,
    mut v_constName_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
    mut v___y_4245_: *mut leanh::LeanObject,
    mut v___y_4246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4247_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_4242_, v_constName_4243_, v___y_4244_, v___y_4245_);
    leanh::lean_dec(v___y_4245_);
    leanh::lean_dec_ref(v___y_4244_);
    leanh::lean_dec(v_ref_4242_);
    return v_res_4247_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(
    mut v_constName_4248_: *mut leanh::LeanObject,
    mut v___y_4249_: *mut leanh::LeanObject,
    mut v___y_4250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4252_ = leanh::lean_ctor_get(v___y_4249_, 5);
    v___x_4253_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_4252_, v_constName_4248_, v___y_4249_, v___y_4250_);
    return v___x_4253_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg___boxed(
    mut v_constName_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4258_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_4254_, v___y_4255_, v___y_4256_);
    leanh::lean_dec(v___y_4256_);
    leanh::lean_dec_ref(v___y_4255_);
    return v_res_4258_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(
    mut v_constName_4259_: *mut leanh::LeanObject,
    mut v___y_4260_: *mut leanh::LeanObject,
    mut v___y_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: u8 = 0;
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4271_: u8 = 0;
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4263_ = lean_st_ref_get(v___y_4261_);
                v_env_4264_ = leanh::lean_ctor_get(v___x_4263_, 0);
                leanh::lean_inc_ref(v_env_4264_);
                leanh::lean_dec(v___x_4263_);
                v___x_4265_ = 0;
                leanh::lean_inc(v_constName_4259_);
                v___x_4266_ =
                    l_Lean_Environment_find_x3f(v_env_4264_, v_constName_4259_, v___x_4265_);
                if leanh::lean_obj_tag(v___x_4266_) == 0 {
                    v___x_4267_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_4259_, v___y_4260_, v___y_4261_);
                    return v___x_4267_;
                } else {
                    leanh::lean_dec(v_constName_4259_);
                    v_val_4268_ = leanh::lean_ctor_get(v___x_4266_, 0);
                    v_isSharedCheck_4275_ = (!leanh::lean_is_exclusive(v___x_4266_)) as u8;
                    if v_isSharedCheck_4275_ == 0 {
                        v___x_4270_ = v___x_4266_;
                        v_isShared_4271_ = v_isSharedCheck_4275_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4268_);
                        leanh::lean_dec(v___x_4266_);
                        v___x_4270_ = leanh::lean_box(0);
                        v_isShared_4271_ = v_isSharedCheck_4275_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4271_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4270_, 0);
                    v___x_4273_ = v___x_4270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_val_4268_);
                    v___x_4273_ = v_reuseFailAlloc_4274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0___boxed(
    mut v_constName_4276_: *mut leanh::LeanObject,
    mut v___y_4277_: *mut leanh::LeanObject,
    mut v___y_4278_: *mut leanh::LeanObject,
    mut v___y_4279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4280_ = l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(
        v_constName_4276_,
        v___y_4277_,
        v___y_4278_,
    );
    leanh::lean_dec(v___y_4278_);
    leanh::lean_dec_ref(v___y_4277_);
    return v_res_4280_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4281_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4281_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__0,
    );
    v___x_4283_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4283_, 0, v___x_4282_);
    return v___x_4283_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = leanh::lean_box(1);
    v___x_4285_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_4286_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1,
    );
    v___x_4287_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4287_, 0, v___x_4286_);
    leanh::lean_ctor_set(v___x_4287_, 1, v___x_4285_);
    leanh::lean_ctor_set(v___x_4287_, 2, v___x_4284_);
    return v___x_4287_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4290_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1,
    );
    v___x_4291_ = leanh::lean_unsigned_to_nat(0);
    v___x_4292_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_4292_, 0, v___x_4291_);
    leanh::lean_ctor_set(v___x_4292_, 1, v___x_4291_);
    leanh::lean_ctor_set(v___x_4292_, 2, v___x_4291_);
    leanh::lean_ctor_set(v___x_4292_, 3, v___x_4291_);
    leanh::lean_ctor_set(v___x_4292_, 4, v___x_4290_);
    leanh::lean_ctor_set(v___x_4292_, 5, v___x_4290_);
    leanh::lean_ctor_set(v___x_4292_, 6, v___x_4290_);
    leanh::lean_ctor_set(v___x_4292_, 7, v___x_4290_);
    leanh::lean_ctor_set(v___x_4292_, 8, v___x_4290_);
    leanh::lean_ctor_set(v___x_4292_, 9, v___x_4290_);
    return v___x_4292_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1,
    );
    v___x_4294_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_4294_, 0, v___x_4293_);
    leanh::lean_ctor_set(v___x_4294_, 1, v___x_4293_);
    leanh::lean_ctor_set(v___x_4294_, 2, v___x_4293_);
    leanh::lean_ctor_set(v___x_4294_, 3, v___x_4293_);
    leanh::lean_ctor_set(v___x_4294_, 4, v___x_4293_);
    leanh::lean_ctor_set(v___x_4294_, 5, v___x_4293_);
    return v___x_4294_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4295_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__1,
    );
    v___x_4296_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_4296_, 0, v___x_4295_);
    leanh::lean_ctor_set(v___x_4296_, 1, v___x_4295_);
    leanh::lean_ctor_set(v___x_4296_, 2, v___x_4295_);
    leanh::lean_ctor_set(v___x_4296_, 3, v___x_4295_);
    leanh::lean_ctor_set(v___x_4296_, 4, v___x_4295_);
    return v___x_4296_;
}
pub unsafe fn _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6_once
        ),
        _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__6,
    );
    v___x_4298_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_compileParserExpr_spec__3_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_4299_ = leanh::lean_box(1);
    v___x_4300_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5_once
        ),
        _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__5,
    );
    v___x_4301_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4_once
        ),
        _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__4,
    );
    v___x_4302_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_4302_, 0, v___x_4301_);
    leanh::lean_ctor_set(v___x_4302_, 1, v___x_4300_);
    leanh::lean_ctor_set(v___x_4302_, 2, v___x_4299_);
    leanh::lean_ctor_set(v___x_4302_, 3, v___x_4298_);
    leanh::lean_ctor_set(v___x_4302_, 4, v___x_4297_);
    return v___x_4302_;
}
pub unsafe fn l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(
    mut v_constName_4311_: *mut leanh::LeanObject,
    mut v_ctx_4312_: *mut leanh::LeanObject,
    mut v_builtin_4313_: u8,
    mut v_catName_4314_: *mut leanh::LeanObject,
    mut v___y_4315_: *mut leanh::LeanObject,
    mut v___y_4316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4319_: u8 = 0;
    let mut v___y_4320_: u8 = 0;
    let mut v___y_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: u8 = 0;
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: u8 = 0;
    let mut v___x_4326_: u8 = 0;
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: u64 = 0;
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut v_a_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4351_: u8 = 0;
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4360_: u8 = 0;
    let mut v___y_4361_: u8 = 0;
    let mut v___y_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4363_: u8 = 0;
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: u8 = 0;
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: u8 = 0;
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: u8 = 0;
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u64 = 0;
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: u8 = 0;
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4396_: u8 = 0;
    let mut v_unused_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4404_: u8 = 0;
    let mut v_unused_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: u8 = 0;
    let mut v___x_4417_: u8 = 0;
    let mut v___x_4418_: u8 = 0;
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: u8 = 0;
    let mut v_a_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4424_: u8 = 0;
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_constName_4311_);
                v___x_4356_ =
                    l_Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0(
                        v_constName_4311_,
                        v___y_4315_,
                        v___y_4316_,
                    );
                if leanh::lean_obj_tag(v___x_4356_) == 0 {
                    v_a_4357_ = leanh::lean_ctor_get(v___x_4356_, 0);
                    leanh::lean_inc(v_a_4357_);
                    leanh::lean_dec_ref_known(v___x_4356_, 1);
                    v___x_4358_ = l_Lean_ConstantInfo_type(v_a_4357_);
                    leanh::lean_dec(v_a_4357_);
                    v___x_4366_ =
                        l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__11;
                    v___x_4418_ = l_Lean_Expr_isConstOf(v___x_4358_, v___x_4366_);
                    if v___x_4418_ == 0 {
                        v___x_4419_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9;
                        v___x_4420_ = l_Lean_Expr_isConstOf(v___x_4358_, v___x_4419_);
                        leanh::lean_dec_ref(v___x_4358_);
                        v___y_4368_ = v___x_4420_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_4358_);
                        v___y_4368_ = v___x_4418_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_ctx_4312_);
                    leanh::lean_dec(v_constName_4311_);
                    v_a_4421_ = leanh::lean_ctor_get(v___x_4356_, 0);
                    v_isSharedCheck_4428_ = (!leanh::lean_is_exclusive(v___x_4356_)) as u8;
                    if v_isSharedCheck_4428_ == 0 {
                        v___x_4423_ = v___x_4356_;
                        v_isShared_4424_ = v_isSharedCheck_4428_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4421_);
                        leanh::lean_dec(v___x_4356_);
                        v___x_4423_ = leanh::lean_box(0);
                        v_isShared_4424_ = v_isSharedCheck_4428_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_4321_) == 0 {
                    v_a_4322_ = leanh::lean_ctor_get(v___y_4321_, 0);
                    leanh::lean_inc(v_a_4322_);
                    leanh::lean_dec_ref_known(v___y_4321_, 1);
                    v___x_4323_ = 0;
                    v___x_4324_ = 1;
                    v___x_4325_ = 0;
                    v___x_4326_ = 2;
                    v___x_4327_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 0 as u32, v___x_4323_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 1 as u32, v___x_4323_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 2 as u32, v___x_4323_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 3 as u32, v___x_4323_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 4 as u32, v___x_4323_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 5 as u32, v___y_4319_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 6 as u32, v___y_4319_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 7 as u32, v___x_4323_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 8 as u32, v___y_4319_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 9 as u32, v___x_4324_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 10 as u32, v___x_4325_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 11 as u32, v___y_4319_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 12 as u32, v___y_4319_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 13 as u32, v___y_4319_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 14 as u32, v___x_4326_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 15 as u32, v___y_4319_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 16 as u32, v___y_4319_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 17 as u32, v___y_4319_);
                    leanh::lean_ctor_set_uint8(v___x_4327_, 18 as u32, v___y_4319_);
                    v___x_4328_ =
                        l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4327_);
                    v___x_4329_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v___x_4329_, 0, v___x_4327_);
                    leanh::lean_ctor_set_uint64(
                        v___x_4329_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_4328_,
                    );
                    v___x_4330_ = leanh::lean_box(1);
                    v___x_4331_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4332_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once), _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2);
                    v___x_4333_ =
                        l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3;
                    v___x_4334_ = leanh::lean_box(0);
                    v___x_4335_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    leanh::lean_ctor_set(v___x_4335_, 0, v___x_4329_);
                    leanh::lean_ctor_set(v___x_4335_, 1, v___x_4330_);
                    leanh::lean_ctor_set(v___x_4335_, 2, v___x_4332_);
                    leanh::lean_ctor_set(v___x_4335_, 3, v___x_4333_);
                    leanh::lean_ctor_set(v___x_4335_, 4, v___x_4334_);
                    leanh::lean_ctor_set(v___x_4335_, 5, v___x_4331_);
                    leanh::lean_ctor_set(v___x_4335_, 6, v___x_4334_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4335_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                        v___x_4323_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4335_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                        v___x_4323_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4335_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                        v___x_4323_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4335_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                        v___y_4320_,
                    );
                    v___x_4336_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once), _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
                    v___x_4337_ = lean_st_mk_ref(v___x_4336_);
                    v___x_4338_ = l_Lean_ParserCompiler_compileEmbeddedParsers___redArg(
                        v_ctx_4312_,
                        v_builtin_4313_,
                        v_a_4322_,
                        v___x_4335_,
                        v___x_4337_,
                        v___y_4315_,
                        v___y_4316_,
                    );
                    leanh::lean_dec_ref_known(v___x_4335_, 7);
                    if leanh::lean_obj_tag(v___x_4338_) == 0 {
                        v_a_4339_ = leanh::lean_ctor_get(v___x_4338_, 0);
                        v_isSharedCheck_4347_ =
                            (!leanh::lean_is_exclusive(v___x_4338_)) as u8;
                        if v_isSharedCheck_4347_ == 0 {
                            v___x_4341_ = v___x_4338_;
                            v_isShared_4342_ = v_isSharedCheck_4347_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4339_);
                            leanh::lean_dec(v___x_4338_);
                            v___x_4341_ = leanh::lean_box(0);
                            v_isShared_4342_ = v_isSharedCheck_4347_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4337_);
                        return v___x_4338_;
                    }
                } else {
                    leanh::lean_dec_ref(v_ctx_4312_);
                    v_a_4348_ = leanh::lean_ctor_get(v___y_4321_, 0);
                    v_isSharedCheck_4355_ = (!leanh::lean_is_exclusive(v___y_4321_)) as u8;
                    if v_isSharedCheck_4355_ == 0 {
                        v___x_4350_ = v___y_4321_;
                        v_isShared_4351_ = v_isSharedCheck_4355_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4348_);
                        leanh::lean_dec(v___y_4321_);
                        v___x_4350_ = leanh::lean_box(0);
                        v_isShared_4351_ = v_isSharedCheck_4355_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4343_ = lean_st_ref_get(v___x_4337_);
                leanh::lean_dec(v___x_4337_);
                leanh::lean_dec(v___x_4343_);
                if v_isShared_4342_ == 0 {
                    v___x_4345_ = v___x_4341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4346_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4339_);
                    v___x_4345_ = v_reuseFailAlloc_4346_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4345_;
            }
            4 => {
                if v_isShared_4351_ == 0 {
                    v___x_4353_ = v___x_4350_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4353_;
            }
            6 => {
                if v___y_4363_ == 0 {
                    leanh::lean_dec_ref(v___y_4362_);
                    v___x_4364_ =
                        l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__9;
                    v___x_4365_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_4364_, v_constName_4311_, v___y_4315_, v___y_4316_);
                    v___y_4319_ = v___y_4360_;
                    v___y_4320_ = v___y_4361_;
                    v___y_4321_ = v___x_4365_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_constName_4311_);
                    v___y_4319_ = v___y_4360_;
                    v___y_4320_ = v___y_4361_;
                    v___y_4321_ = v___y_4362_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_4369_ = 1;
                if v___y_4368_ == 0 {
                    v___x_4370_ = 1;
                    v___x_4371_ = 0;
                    v___x_4372_ = 2;
                    v___x_4373_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 0 as u32, v___y_4368_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 1 as u32, v___y_4368_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 2 as u32, v___y_4368_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 3 as u32, v___y_4368_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 4 as u32, v___y_4368_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 5 as u32, v___x_4369_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 6 as u32, v___x_4369_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 7 as u32, v___y_4368_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 8 as u32, v___x_4369_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 9 as u32, v___x_4370_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 10 as u32, v___x_4371_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 11 as u32, v___x_4369_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 12 as u32, v___x_4369_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 13 as u32, v___x_4369_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 14 as u32, v___x_4372_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 15 as u32, v___x_4369_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 16 as u32, v___x_4369_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 17 as u32, v___x_4369_);
                    leanh::lean_ctor_set_uint8(v___x_4373_, 18 as u32, v___x_4369_);
                    v___x_4374_ =
                        l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4373_);
                    v___x_4375_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v___x_4375_, 0, v___x_4373_);
                    leanh::lean_ctor_set_uint64(
                        v___x_4375_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_4374_,
                    );
                    v___x_4376_ = leanh::lean_box(1);
                    v___x_4377_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4378_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2_once), _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__2);
                    v___x_4379_ =
                        l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__3;
                    v___x_4380_ = leanh::lean_box(0);
                    v___x_4381_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    leanh::lean_ctor_set(v___x_4381_, 0, v___x_4375_);
                    leanh::lean_ctor_set(v___x_4381_, 1, v___x_4376_);
                    leanh::lean_ctor_set(v___x_4381_, 2, v___x_4378_);
                    leanh::lean_ctor_set(v___x_4381_, 3, v___x_4379_);
                    leanh::lean_ctor_set(v___x_4381_, 4, v___x_4380_);
                    leanh::lean_ctor_set(v___x_4381_, 5, v___x_4377_);
                    leanh::lean_ctor_set(v___x_4381_, 6, v___x_4380_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4381_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                        v___y_4368_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4381_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                        v___y_4368_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4381_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                        v___y_4368_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4381_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                        v___x_4369_,
                    );
                    v___x_4382_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7_once), _init_l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___closed__7);
                    v___x_4383_ = lean_st_mk_ref(v___x_4382_);
                    v___x_4384_ = l_Lean_Name_isAnonymous(v_catName_4314_);
                    v___x_4385_ = leanh::lean_box(0);
                    v___x_4386_ = l_Lean_mkConst(v_constName_4311_, v___x_4385_);
                    v___x_4387_ = leanh::lean_box(0);
                    v___x_4388_ = l_Lean_ParserCompiler_compileParserExpr___redArg(
                        v_ctx_4312_,
                        v_builtin_4313_,
                        v___x_4384_,
                        v___x_4386_,
                        v___x_4381_,
                        v___x_4383_,
                        v___y_4315_,
                        v___y_4316_,
                    );
                    leanh::lean_dec_ref_known(v___x_4381_, 7);
                    if leanh::lean_obj_tag(v___x_4388_) == 0 {
                        v_isSharedCheck_4396_ =
                            (!leanh::lean_is_exclusive(v___x_4388_)) as u8;
                        if v_isSharedCheck_4396_ == 0 {
                            v_unused_4397_ = leanh::lean_ctor_get(v___x_4388_, 0);
                            leanh::lean_dec(v_unused_4397_);
                            v___x_4390_ = v___x_4388_;
                            v_isShared_4391_ = v_isSharedCheck_4396_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4388_);
                            v___x_4390_ = leanh::lean_box(0);
                            v_isShared_4391_ = v_isSharedCheck_4396_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4383_);
                        if leanh::lean_obj_tag(v___x_4388_) == 0 {
                            v_isSharedCheck_4404_ =
                                (!leanh::lean_is_exclusive(v___x_4388_)) as u8;
                            if v_isSharedCheck_4404_ == 0 {
                                v_unused_4405_ = leanh::lean_ctor_get(v___x_4388_, 0);
                                leanh::lean_dec(v_unused_4405_);
                                v___x_4399_ = v___x_4388_;
                                v_isShared_4400_ = v_isSharedCheck_4404_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_4388_);
                                v___x_4399_ = leanh::lean_box(0);
                                v_isShared_4400_ = v_isSharedCheck_4404_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v_a_4406_ = leanh::lean_ctor_get(v___x_4388_, 0);
                            v_isSharedCheck_4413_ =
                                (!leanh::lean_is_exclusive(v___x_4388_)) as u8;
                            if v_isSharedCheck_4413_ == 0 {
                                v___x_4408_ = v___x_4388_;
                                v_isShared_4409_ = v_isSharedCheck_4413_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4406_);
                                leanh::lean_dec(v___x_4388_);
                                v___x_4408_ = leanh::lean_box(0);
                                v_isShared_4409_ = v_isSharedCheck_4413_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_inc(v_constName_4311_);
                    v___x_4414_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(v___x_4366_, v_constName_4311_, v___y_4315_, v___y_4316_);
                    if leanh::lean_obj_tag(v___x_4414_) == 0 {
                        leanh::lean_dec(v_constName_4311_);
                        v___y_4319_ = v___y_4368_;
                        v___y_4320_ = v___x_4369_;
                        v___y_4321_ = v___x_4414_;
                        state = 1;
                        continue;
                    } else {
                        v_a_4415_ = leanh::lean_ctor_get(v___x_4414_, 0);
                        leanh::lean_inc(v_a_4415_);
                        v___x_4416_ = l_Lean_Exception_isInterrupt(v_a_4415_);
                        if v___x_4416_ == 0 {
                            v___x_4417_ = l_Lean_Exception_isRuntime(v_a_4415_);
                            v___y_4360_ = v___y_4368_;
                            v___y_4361_ = v___x_4369_;
                            v___y_4362_ = v___x_4414_;
                            v___y_4363_ = v___x_4417_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_4415_);
                            v___y_4360_ = v___y_4368_;
                            v___y_4361_ = v___x_4369_;
                            v___y_4362_ = v___x_4414_;
                            v___y_4363_ = v___x_4416_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_4392_ = lean_st_ref_get(v___x_4383_);
                leanh::lean_dec(v___x_4383_);
                leanh::lean_dec(v___x_4392_);
                if v_isShared_4391_ == 0 {
                    leanh::lean_ctor_set(v___x_4390_, 0, v___x_4387_);
                    v___x_4394_ = v___x_4390_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4395_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4387_);
                    v___x_4394_ = v_reuseFailAlloc_4395_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4394_;
            }
            10 => {
                if v_isShared_4400_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4399_, 0);
                    leanh::lean_ctor_set(v___x_4399_, 0, v___x_4387_);
                    v___x_4402_ = v___x_4399_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4403_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4387_);
                    v___x_4402_ = v_reuseFailAlloc_4403_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4402_;
            }
            12 => {
                if v_isShared_4409_ == 0 {
                    v___x_4411_ = v___x_4408_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
                    v___x_4411_ = v_reuseFailAlloc_4412_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4411_;
            }
            14 => {
                if v_isShared_4424_ == 0 {
                    v___x_4426_ = v___x_4423_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
                    v___x_4426_ = v_reuseFailAlloc_4427_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed(
    mut v_constName_4429_: *mut leanh::LeanObject,
    mut v_ctx_4430_: *mut leanh::LeanObject,
    mut v_builtin_4431_: *mut leanh::LeanObject,
    mut v_catName_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
    mut v___y_4434_: *mut leanh::LeanObject,
    mut v___y_4435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_boxed_4436_: u8 = 0;
    let mut v_res_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_4436_ = (leanh::lean_unbox(v_builtin_4431_) as u8);
    v_res_4437_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0(
        v_constName_4429_,
        v_ctx_4430_,
        v_builtin_boxed_4436_,
        v_catName_4432_,
        v___y_4433_,
        v___y_4434_,
    );
    leanh::lean_dec(v___y_4434_);
    leanh::lean_dec_ref(v___y_4433_);
    leanh::lean_dec(v_catName_4432_);
    return v_res_4437_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(
    mut v___y_4438_: *mut leanh::LeanObject,
    mut v_isExporting_4439_: u8,
    mut v___x_4440_: *mut leanh::LeanObject,
    mut v_a_x3f_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4462_: u8 = 0;
    let mut v_unused_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4443_ = lean_st_ref_take(v___y_4438_);
                v_env_4444_ = leanh::lean_ctor_get(v___x_4443_, 0);
                v_nextMacroScope_4445_ = leanh::lean_ctor_get(v___x_4443_, 1);
                v_ngen_4446_ = leanh::lean_ctor_get(v___x_4443_, 2);
                v_auxDeclNGen_4447_ = leanh::lean_ctor_get(v___x_4443_, 3);
                v_traceState_4448_ = leanh::lean_ctor_get(v___x_4443_, 4);
                v_messages_4449_ = leanh::lean_ctor_get(v___x_4443_, 6);
                v_infoState_4450_ = leanh::lean_ctor_get(v___x_4443_, 7);
                v_snapshotTasks_4451_ = leanh::lean_ctor_get(v___x_4443_, 8);
                v_isSharedCheck_4462_ = (!leanh::lean_is_exclusive(v___x_4443_)) as u8;
                if v_isSharedCheck_4462_ == 0 {
                    v_unused_4463_ = leanh::lean_ctor_get(v___x_4443_, 5);
                    leanh::lean_dec(v_unused_4463_);
                    v___x_4453_ = v___x_4443_;
                    v_isShared_4454_ = v_isSharedCheck_4462_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4451_);
                    leanh::lean_inc(v_infoState_4450_);
                    leanh::lean_inc(v_messages_4449_);
                    leanh::lean_inc(v_traceState_4448_);
                    leanh::lean_inc(v_auxDeclNGen_4447_);
                    leanh::lean_inc(v_ngen_4446_);
                    leanh::lean_inc(v_nextMacroScope_4445_);
                    leanh::lean_inc(v_env_4444_);
                    leanh::lean_dec(v___x_4443_);
                    v___x_4453_ = leanh::lean_box(0);
                    v_isShared_4454_ = v_isSharedCheck_4462_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4455_ = l_Lean_Environment_setExporting(v_env_4444_, v_isExporting_4439_);
                if v_isShared_4454_ == 0 {
                    leanh::lean_ctor_set(v___x_4453_, 5, v___x_4440_);
                    leanh::lean_ctor_set(v___x_4453_, 0, v___x_4455_);
                    v___x_4457_ = v___x_4453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4461_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 1, v_nextMacroScope_4445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 2, v_ngen_4446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 3, v_auxDeclNGen_4447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 4, v_traceState_4448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 5, v___x_4440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 6, v_messages_4449_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 7, v_infoState_4450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4461_, 8, v_snapshotTasks_4451_);
                    v___x_4457_ = v_reuseFailAlloc_4461_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4458_ = lean_st_ref_set(v___y_4438_, v___x_4457_);
                v___x_4459_ = leanh::lean_box(0);
                v___x_4460_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4460_, 0, v___x_4459_);
                return v___x_4460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0___boxed(
    mut v___y_4464_: *mut leanh::LeanObject,
    mut v_isExporting_4465_: *mut leanh::LeanObject,
    mut v___x_4466_: *mut leanh::LeanObject,
    mut v_a_x3f_4467_: *mut leanh::LeanObject,
    mut v___y_4468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4469_: u8 = 0;
    let mut v_res_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4469_ = (leanh::lean_unbox(v_isExporting_4465_) as u8);
    v_res_4470_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_4464_, v_isExporting_boxed_4469_, v___x_4466_, v_a_x3f_4467_);
    leanh::lean_dec(v_a_x3f_4467_);
    leanh::lean_dec(v___y_4464_);
    return v_res_4470_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(
    mut v_x_4471_: *mut leanh::LeanObject,
    mut v_isExporting_4472_: u8,
    mut v___y_4473_: *mut leanh::LeanObject,
    mut v___y_4474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4478_: u8 = 0;
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4490_: u8 = 0;
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4510_: u8 = 0;
    let mut v_unused_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_a_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4519_: u8 = 0;
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_unused_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4526_: u8 = 0;
    let mut v_unused_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4476_ = lean_st_ref_get(v___y_4474_);
                v_env_4477_ = leanh::lean_ctor_get(v___x_4476_, 0);
                leanh::lean_inc_ref(v_env_4477_);
                leanh::lean_dec(v___x_4476_);
                v_isExporting_4478_ = leanh::lean_ctor_get_uint8(
                    v_env_4477_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_4477_);
                v___x_4479_ = lean_st_ref_take(v___y_4474_);
                v_env_4480_ = leanh::lean_ctor_get(v___x_4479_, 0);
                v_nextMacroScope_4481_ = leanh::lean_ctor_get(v___x_4479_, 1);
                v_ngen_4482_ = leanh::lean_ctor_get(v___x_4479_, 2);
                v_auxDeclNGen_4483_ = leanh::lean_ctor_get(v___x_4479_, 3);
                v_traceState_4484_ = leanh::lean_ctor_get(v___x_4479_, 4);
                v_messages_4485_ = leanh::lean_ctor_get(v___x_4479_, 6);
                v_infoState_4486_ = leanh::lean_ctor_get(v___x_4479_, 7);
                v_snapshotTasks_4487_ = leanh::lean_ctor_get(v___x_4479_, 8);
                v_isSharedCheck_4526_ = (!leanh::lean_is_exclusive(v___x_4479_)) as u8;
                if v_isSharedCheck_4526_ == 0 {
                    v_unused_4527_ = leanh::lean_ctor_get(v___x_4479_, 5);
                    leanh::lean_dec(v_unused_4527_);
                    v___x_4489_ = v___x_4479_;
                    v_isShared_4490_ = v_isSharedCheck_4526_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4487_);
                    leanh::lean_inc(v_infoState_4486_);
                    leanh::lean_inc(v_messages_4485_);
                    leanh::lean_inc(v_traceState_4484_);
                    leanh::lean_inc(v_auxDeclNGen_4483_);
                    leanh::lean_inc(v_ngen_4482_);
                    leanh::lean_inc(v_nextMacroScope_4481_);
                    leanh::lean_inc(v_env_4480_);
                    leanh::lean_dec(v___x_4479_);
                    v___x_4489_ = leanh::lean_box(0);
                    v_isShared_4490_ = v_isSharedCheck_4526_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4491_ = l_Lean_Environment_setExporting(v_env_4480_, v_isExporting_4472_);
                v___x_4492_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7_once
                    ),
                    _init_l_Lean_ParserCompiler_compileParserExpr___redArg___closed__7,
                );
                if v_isShared_4490_ == 0 {
                    leanh::lean_ctor_set(v___x_4489_, 5, v___x_4492_);
                    leanh::lean_ctor_set(v___x_4489_, 0, v___x_4491_);
                    v___x_4494_ = v___x_4489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4525_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_nextMacroScope_4481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 2, v_ngen_4482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 3, v_auxDeclNGen_4483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 4, v_traceState_4484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 5, v___x_4492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 6, v_messages_4485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 7, v_infoState_4486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 8, v_snapshotTasks_4487_);
                    v___x_4494_ = v_reuseFailAlloc_4525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4495_ = lean_st_ref_set(v___y_4474_, v___x_4494_);
                leanh::lean_inc(v___y_4474_);
                leanh::lean_inc_ref(v___y_4473_);
                v_r_4496_ = leanh::lean_apply_3(
                    v_x_4471_,
                    v___y_4473_,
                    v___y_4474_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_4496_) == 0 {
                    v_a_4497_ = leanh::lean_ctor_get(v_r_4496_, 0);
                    v_isSharedCheck_4513_ = (!leanh::lean_is_exclusive(v_r_4496_)) as u8;
                    if v_isSharedCheck_4513_ == 0 {
                        v___x_4499_ = v_r_4496_;
                        v_isShared_4500_ = v_isSharedCheck_4513_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4497_);
                        leanh::lean_dec(v_r_4496_);
                        v___x_4499_ = leanh::lean_box(0);
                        v_isShared_4500_ = v_isSharedCheck_4513_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4514_ = leanh::lean_ctor_get(v_r_4496_, 0);
                    leanh::lean_inc(v_a_4514_);
                    leanh::lean_dec_ref_known(v_r_4496_, 1);
                    v___x_4515_ = leanh::lean_box(0);
                    v___x_4516_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_4474_, v_isExporting_4478_, v___x_4492_, v___x_4515_);
                    v_isSharedCheck_4523_ = (!leanh::lean_is_exclusive(v___x_4516_)) as u8;
                    if v_isSharedCheck_4523_ == 0 {
                        v_unused_4524_ = leanh::lean_ctor_get(v___x_4516_, 0);
                        leanh::lean_dec(v_unused_4524_);
                        v___x_4518_ = v___x_4516_;
                        v_isShared_4519_ = v_isSharedCheck_4523_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4516_);
                        v___x_4518_ = leanh::lean_box(0);
                        v_isShared_4519_ = v_isSharedCheck_4523_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_a_4497_);
                if v_isShared_4500_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4499_, 1);
                    v___x_4502_ = v___x_4499_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4497_);
                    v___x_4502_ = v_reuseFailAlloc_4512_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4503_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___lam__0(v___y_4474_, v_isExporting_4478_, v___x_4492_, v___x_4502_);
                leanh::lean_dec_ref(v___x_4502_);
                v_isSharedCheck_4510_ = (!leanh::lean_is_exclusive(v___x_4503_)) as u8;
                if v_isSharedCheck_4510_ == 0 {
                    v_unused_4511_ = leanh::lean_ctor_get(v___x_4503_, 0);
                    leanh::lean_dec(v_unused_4511_);
                    v___x_4505_ = v___x_4503_;
                    v_isShared_4506_ = v_isSharedCheck_4510_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4503_);
                    v___x_4505_ = leanh::lean_box(0);
                    v_isShared_4506_ = v_isSharedCheck_4510_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4506_ == 0 {
                    leanh::lean_ctor_set(v___x_4505_, 0, v_a_4497_);
                    v___x_4508_ = v___x_4505_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4497_);
                    v___x_4508_ = v_reuseFailAlloc_4509_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4508_;
            }
            7 => {
                if v_isShared_4519_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4518_, 1);
                    leanh::lean_ctor_set(v___x_4518_, 0, v_a_4514_);
                    v___x_4521_ = v___x_4518_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4522_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4514_);
                    v___x_4521_ = v_reuseFailAlloc_4522_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg___boxed(
    mut v_x_4528_: *mut leanh::LeanObject,
    mut v_isExporting_4529_: *mut leanh::LeanObject,
    mut v___y_4530_: *mut leanh::LeanObject,
    mut v___y_4531_: *mut leanh::LeanObject,
    mut v___y_4532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4533_: u8 = 0;
    let mut v_res_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4533_ = (leanh::lean_unbox(v_isExporting_4529_) as u8);
    v_res_4534_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_4528_, v_isExporting_boxed_4533_, v___y_4530_, v___y_4531_);
    leanh::lean_dec(v___y_4531_);
    leanh::lean_dec_ref(v___y_4530_);
    return v_res_4534_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(
    mut v_x_4535_: *mut leanh::LeanObject,
    mut v_when_4536_: u8,
    mut v___y_4537_: *mut leanh::LeanObject,
    mut v___y_4538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_4536_ == 0 {
        let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_4538_);
        leanh::lean_inc_ref(v___y_4537_);
        v___x_4540_ = leanh::lean_apply_3(
            v_x_4535_,
            v___y_4537_,
            v___y_4538_,
            leanh::lean_box(0),
        );
        return v___x_4540_;
    } else {
        let mut v___x_4541_: u8 = 0;
        let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4541_ = 0;
        v___x_4542_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_4535_, v___x_4541_, v___y_4537_, v___y_4538_);
        return v___x_4542_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg___boxed(
    mut v_x_4543_: *mut leanh::LeanObject,
    mut v_when_4544_: *mut leanh::LeanObject,
    mut v___y_4545_: *mut leanh::LeanObject,
    mut v___y_4546_: *mut leanh::LeanObject,
    mut v___y_4547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_4548_: u8 = 0;
    let mut v_res_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4548_ = (leanh::lean_unbox(v_when_4544_) as u8);
    v_res_4549_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_4543_, v_when_boxed_4548_, v___y_4545_, v___y_4546_);
    leanh::lean_dec(v___y_4546_);
    leanh::lean_dec_ref(v___y_4545_);
    return v_res_4549_;
}
pub unsafe fn l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(
    mut v_ctx_4550_: *mut leanh::LeanObject,
    mut v_catName_4551_: *mut leanh::LeanObject,
    mut v_constName_4552_: *mut leanh::LeanObject,
    mut v_builtin_4553_: u8,
    mut v___y_4554_: *mut leanh::LeanObject,
    mut v___y_4555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4557_ = leanh::lean_box((v_builtin_4553_) as usize);
    v___f_4558_ = leanh::lean_alloc_closure(
        l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_4558_, 0, v_constName_4552_);
    leanh::lean_closure_set(v___f_4558_, 1, v_ctx_4550_);
    leanh::lean_closure_set(v___f_4558_, 2, v___x_4557_);
    leanh::lean_closure_set(v___f_4558_, 3, v_catName_4551_);
    v___x_4559_ = 1;
    v___x_4560_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v___f_4558_, v___x_4559_, v___y_4554_, v___y_4555_);
    return v___x_4560_;
}
pub unsafe fn l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed(
    mut v_ctx_4561_: *mut leanh::LeanObject,
    mut v_catName_4562_: *mut leanh::LeanObject,
    mut v_constName_4563_: *mut leanh::LeanObject,
    mut v_builtin_4564_: *mut leanh::LeanObject,
    mut v___y_4565_: *mut leanh::LeanObject,
    mut v___y_4566_: *mut leanh::LeanObject,
    mut v___y_4567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_boxed_4568_: u8 = 0;
    let mut v_res_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_4568_ = (leanh::lean_unbox(v_builtin_4564_) as u8);
    v_res_4569_ = l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1(
        v_ctx_4561_,
        v_catName_4562_,
        v_constName_4563_,
        v_builtin_boxed_4568_,
        v___y_4565_,
        v___y_4566_,
    );
    leanh::lean_dec(v___y_4566_);
    leanh::lean_dec_ref(v___y_4565_);
    return v_res_4569_;
}
pub unsafe fn l_Lean_ParserCompiler_registerParserCompiler___redArg(
    mut v_ctx_4570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4572_ = leanh::lean_alloc_closure(
        l_Lean_ParserCompiler_registerParserCompiler___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_4572_, 0, v_ctx_4570_);
    v___x_4573_ = l_Lean_Parser_registerParserAttributeHook(v___f_4572_);
    return v___x_4573_;
}
pub unsafe fn l_Lean_ParserCompiler_registerParserCompiler___redArg___boxed(
    mut v_ctx_4574_: *mut leanh::LeanObject,
    mut v_a_4575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4576_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_4574_);
    return v_res_4576_;
}
pub unsafe fn l_Lean_ParserCompiler_registerParserCompiler(
    mut v_00_u03b1_4577_: *mut leanh::LeanObject,
    mut v_ctx_4578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4580_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v_ctx_4578_);
    return v___x_4580_;
}
pub unsafe fn l_Lean_ParserCompiler_registerParserCompiler___boxed(
    mut v_00_u03b1_4581_: *mut leanh::LeanObject,
    mut v_ctx_4582_: *mut leanh::LeanObject,
    mut v_a_4583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4584_ = l_Lean_ParserCompiler_registerParserCompiler(v_00_u03b1_4581_, v_ctx_4582_);
    return v_res_4584_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(
    mut v_00_u03b1_4585_: *mut leanh::LeanObject,
    mut v___y_4586_: *mut leanh::LeanObject,
    mut v___y_4587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4589_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___redArg();
    return v___x_4589_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3___boxed(
    mut v_00_u03b1_4590_: *mut leanh::LeanObject,
    mut v___y_4591_: *mut leanh::LeanObject,
    mut v___y_4592_: *mut leanh::LeanObject,
    mut v___y_4593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4594_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__3(v_00_u03b1_4590_, v___y_4591_, v___y_4592_);
    leanh::lean_dec(v___y_4592_);
    leanh::lean_dec_ref(v___y_4591_);
    return v_res_4594_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(
    mut v_00_u03b1_4595_: *mut leanh::LeanObject,
    mut v_typeName_4596_: *mut leanh::LeanObject,
    mut v_constName_4597_: *mut leanh::LeanObject,
    mut v___y_4598_: *mut leanh::LeanObject,
    mut v___y_4599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4601_ =
        l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___redArg(
            v_typeName_4596_,
            v_constName_4597_,
            v___y_4598_,
            v___y_4599_,
        );
    return v___x_4601_;
}
pub unsafe fn l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1___boxed(
    mut v_00_u03b1_4602_: *mut leanh::LeanObject,
    mut v_typeName_4603_: *mut leanh::LeanObject,
    mut v_constName_4604_: *mut leanh::LeanObject,
    mut v___y_4605_: *mut leanh::LeanObject,
    mut v___y_4606_: *mut leanh::LeanObject,
    mut v___y_4607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4608_ = l_Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1(
        v_00_u03b1_4602_,
        v_typeName_4603_,
        v_constName_4604_,
        v___y_4605_,
        v___y_4606_,
    );
    leanh::lean_dec(v___y_4606_);
    leanh::lean_dec_ref(v___y_4605_);
    return v_res_4608_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(
    mut v_00_u03b1_4609_: *mut leanh::LeanObject,
    mut v_x_4610_: *mut leanh::LeanObject,
    mut v_isExporting_4611_: u8,
    mut v___y_4612_: *mut leanh::LeanObject,
    mut v___y_4613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4615_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___redArg(v_x_4610_, v_isExporting_4611_, v___y_4612_, v___y_4613_);
    return v___x_4615_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5___boxed(
    mut v_00_u03b1_4616_: *mut leanh::LeanObject,
    mut v_x_4617_: *mut leanh::LeanObject,
    mut v_isExporting_4618_: *mut leanh::LeanObject,
    mut v___y_4619_: *mut leanh::LeanObject,
    mut v___y_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4622_: u8 = 0;
    let mut v_res_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4622_ = (leanh::lean_unbox(v_isExporting_4618_) as u8);
    v_res_4623_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2_spec__5(v_00_u03b1_4616_, v_x_4617_, v_isExporting_boxed_4622_, v___y_4619_, v___y_4620_);
    leanh::lean_dec(v___y_4620_);
    leanh::lean_dec_ref(v___y_4619_);
    return v_res_4623_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(
    mut v_00_u03b1_4624_: *mut leanh::LeanObject,
    mut v_x_4625_: *mut leanh::LeanObject,
    mut v_when_4626_: u8,
    mut v___y_4627_: *mut leanh::LeanObject,
    mut v___y_4628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4630_ = l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___redArg(v_x_4625_, v_when_4626_, v___y_4627_, v___y_4628_);
    return v___x_4630_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2___boxed(
    mut v_00_u03b1_4631_: *mut leanh::LeanObject,
    mut v_x_4632_: *mut leanh::LeanObject,
    mut v_when_4633_: *mut leanh::LeanObject,
    mut v___y_4634_: *mut leanh::LeanObject,
    mut v___y_4635_: *mut leanh::LeanObject,
    mut v___y_4636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_4637_: u8 = 0;
    let mut v_res_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4637_ = (leanh::lean_unbox(v_when_4633_) as u8);
    v_res_4638_ =
        l_Lean_withoutExporting___at___00Lean_ParserCompiler_registerParserCompiler_spec__2(
            v_00_u03b1_4631_,
            v_x_4632_,
            v_when_boxed_4637_,
            v___y_4634_,
            v___y_4635_,
        );
    leanh::lean_dec(v___y_4635_);
    leanh::lean_dec_ref(v___y_4634_);
    return v_res_4638_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(
    mut v_00_u03b1_4639_: *mut leanh::LeanObject,
    mut v_constName_4640_: *mut leanh::LeanObject,
    mut v___y_4641_: *mut leanh::LeanObject,
    mut v___y_4642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___redArg(v_constName_4640_, v___y_4641_, v___y_4642_);
    return v___x_4644_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0___boxed(
    mut v_00_u03b1_4645_: *mut leanh::LeanObject,
    mut v_constName_4646_: *mut leanh::LeanObject,
    mut v___y_4647_: *mut leanh::LeanObject,
    mut v___y_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4650_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0(v_00_u03b1_4645_, v_constName_4646_, v___y_4647_, v___y_4648_);
    leanh::lean_dec(v___y_4648_);
    leanh::lean_dec_ref(v___y_4647_);
    return v_res_4650_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(
    mut v_00_u03b1_4651_: *mut leanh::LeanObject,
    mut v_x_4652_: *mut leanh::LeanObject,
    mut v___y_4653_: *mut leanh::LeanObject,
    mut v___y_4654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4656_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___redArg(v_x_4652_, v___y_4653_, v___y_4654_);
    return v___x_4656_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2___boxed(
    mut v_00_u03b1_4657_: *mut leanh::LeanObject,
    mut v_x_4658_: *mut leanh::LeanObject,
    mut v___y_4659_: *mut leanh::LeanObject,
    mut v___y_4660_: *mut leanh::LeanObject,
    mut v___y_4661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2(v_00_u03b1_4657_, v_x_4658_, v___y_4659_, v___y_4660_);
    leanh::lean_dec(v___y_4660_);
    leanh::lean_dec_ref(v___y_4659_);
    return v_res_4662_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4663_: *mut leanh::LeanObject,
    mut v_ref_4664_: *mut leanh::LeanObject,
    mut v_constName_4665_: *mut leanh::LeanObject,
    mut v___y_4666_: *mut leanh::LeanObject,
    mut v___y_4667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4669_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___redArg(v_ref_4664_, v_constName_4665_, v___y_4666_, v___y_4667_);
    return v___x_4669_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4670_: *mut leanh::LeanObject,
    mut v_ref_4671_: *mut leanh::LeanObject,
    mut v_constName_4672_: *mut leanh::LeanObject,
    mut v___y_4673_: *mut leanh::LeanObject,
    mut v___y_4674_: *mut leanh::LeanObject,
    mut v___y_4675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4676_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1(v_00_u03b1_4670_, v_ref_4671_, v_constName_4672_, v___y_4673_, v___y_4674_);
    leanh::lean_dec(v___y_4674_);
    leanh::lean_dec_ref(v___y_4673_);
    leanh::lean_dec(v_ref_4671_);
    return v_res_4676_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(
    mut v_00_u03b1_4677_: *mut leanh::LeanObject,
    mut v_msg_4678_: *mut leanh::LeanObject,
    mut v___y_4679_: *mut leanh::LeanObject,
    mut v___y_4680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4682_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___redArg(v_msg_4678_, v___y_4679_, v___y_4680_);
    return v___x_4682_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_4683_: *mut leanh::LeanObject,
    mut v_msg_4684_: *mut leanh::LeanObject,
    mut v___y_4685_: *mut leanh::LeanObject,
    mut v___y_4686_: *mut leanh::LeanObject,
    mut v___y_4687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4688_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_ParserCompiler_registerParserCompiler_spec__1_spec__2_spec__4(v_00_u03b1_4683_, v_msg_4684_, v___y_4685_, v___y_4686_);
    leanh::lean_dec(v___y_4686_);
    leanh::lean_dec_ref(v___y_4685_);
    return v_res_4688_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(
    mut v_00_u03b1_4689_: *mut leanh::LeanObject,
    mut v_ref_4690_: *mut leanh::LeanObject,
    mut v_msg_4691_: *mut leanh::LeanObject,
    mut v_declHint_4692_: *mut leanh::LeanObject,
    mut v___y_4693_: *mut leanh::LeanObject,
    mut v___y_4694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4696_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_4690_, v_msg_4691_, v_declHint_4692_, v___y_4693_, v___y_4694_);
    return v___x_4696_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_00_u03b1_4697_: *mut leanh::LeanObject,
    mut v_ref_4698_: *mut leanh::LeanObject,
    mut v_msg_4699_: *mut leanh::LeanObject,
    mut v_declHint_4700_: *mut leanh::LeanObject,
    mut v___y_4701_: *mut leanh::LeanObject,
    mut v___y_4702_: *mut leanh::LeanObject,
    mut v___y_4703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4704_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_4697_, v_ref_4698_, v_msg_4699_, v_declHint_4700_, v___y_4701_, v___y_4702_);
    leanh::lean_dec(v___y_4702_);
    leanh::lean_dec_ref(v___y_4701_);
    leanh::lean_dec(v_ref_4698_);
    return v_res_4704_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(
    mut v_msg_4705_: *mut leanh::LeanObject,
    mut v_declHint_4706_: *mut leanh::LeanObject,
    mut v___y_4707_: *mut leanh::LeanObject,
    mut v___y_4708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4710_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___redArg(v_msg_4705_, v_declHint_4706_, v___y_4708_);
    return v___x_4710_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11___boxed(
    mut v_msg_4711_: *mut leanh::LeanObject,
    mut v_declHint_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
    mut v___y_4714_: *mut leanh::LeanObject,
    mut v___y_4715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4716_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__8_spec__11(v_msg_4711_, v_declHint_4712_, v___y_4713_, v___y_4714_);
    leanh::lean_dec(v___y_4714_);
    leanh::lean_dec_ref(v___y_4713_);
    return v_res_4716_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(
    mut v_00_u03b1_4717_: *mut leanh::LeanObject,
    mut v_ref_4718_: *mut leanh::LeanObject,
    mut v_msg_4719_: *mut leanh::LeanObject,
    mut v___y_4720_: *mut leanh::LeanObject,
    mut v___y_4721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4723_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_4718_, v_msg_4719_, v___y_4720_, v___y_4721_);
    return v___x_4723_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(
    mut v_00_u03b1_4724_: *mut leanh::LeanObject,
    mut v_ref_4725_: *mut leanh::LeanObject,
    mut v_msg_4726_: *mut leanh::LeanObject,
    mut v___y_4727_: *mut leanh::LeanObject,
    mut v___y_4728_: *mut leanh::LeanObject,
    mut v___y_4729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4730_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_ParserCompiler_registerParserCompiler_spec__0_spec__0_spec__1_spec__6_spec__9(v_00_u03b1_4724_, v_ref_4725_, v_msg_4726_, v___y_4727_, v___y_4728_);
    leanh::lean_dec(v___y_4728_);
    leanh::lean_dec_ref(v___y_4727_);
    leanh::lean_dec(v_ref_4725_);
    return v_res_4730_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ParserCompiler(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_ReduceEval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_KeyedDeclsAttribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ParserCompiler_Attribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ParserCompiler(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ParserCompiler(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_ReduceEval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_KeyedDeclsAttribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ParserCompiler_Attribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ParserCompiler(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ParserCompiler(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_ParserCompiler(builtin);
}