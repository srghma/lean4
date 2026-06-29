// Lean compiler output
// Module: Lean.Meta.RecursorInfo
// Imports: Lean.Meta.Basic Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Basic::{
    l_instToStringBool___lam__0___boxed, l_instToStringOption___redArg___lam__0,
};
use crate::r#gen::Init::Data::ToString::Extra::l_List_toString___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNatLit_x3f;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getKind, l_Lean_replaceRef, l_List_lengthTR___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::{
    l_Lean_ParametricAttribute_getParam_x3f___redArg, l_Lean_registerParametricAttribute___redArg,
};
use crate::r#gen::Lean::AuxRecursor::{
    l_Lean_brecOnSuffix, l_Lean_casesOnSuffix, l_Lean_isAuxRecursor, l_Lean_recOnSuffix,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_type, l_Lean_mkRecName,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isInstImplicit, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_isFVar, l_Lean_Expr_isSort, l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_binderInfo;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_FVarId_getDecl___redArg, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_isExprDefEq,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Level::lean_level_eq;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::Util::FindExpr::lean_find_expr;
pub static l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0___closed__0_value:
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
        60, 109, 111, 116, 105, 118, 101, 45, 117, 110, 105, 118, 62, 0,
    ],
};
static mut l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0_value:
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
    m_fun: l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instToStringRecursorUnivLevelPos: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__0_value:
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
        123, 10, 32, 32, 110, 97, 109, 101, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 58, 61, 32,
        0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__1_value:
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
    m_data: [10, 0],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__2_value:
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
        32, 32, 110, 117, 109, 65, 114, 103, 115, 32, 32, 32, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__3_value:
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
        32, 32, 110, 117, 109, 80, 97, 114, 97, 109, 115, 32, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__4_value:
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
        32, 32, 110, 117, 109, 73, 110, 100, 105, 99, 101, 115, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__5_value:
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
        32, 32, 110, 117, 109, 77, 105, 110, 111, 114, 115, 32, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__6_value:
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
        32, 32, 109, 97, 106, 111, 114, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__7_value:
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
        32, 32, 109, 111, 116, 105, 118, 101, 32, 32, 32, 32, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__8_value:
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
        32, 32, 112, 97, 114, 97, 109, 115, 65, 116, 77, 97, 106, 111, 114, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__9_value:
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
        32, 32, 105, 110, 100, 105, 99, 101, 115, 65, 116, 77, 97, 106, 111, 114, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__10_value:
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
        32, 32, 112, 114, 111, 100, 117, 99, 101, 77, 111, 116, 105, 118, 101, 32, 32, 58, 61, 32,
        0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__11_value:
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
    m_data: [125, 0],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__12_value:
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
        32, 32, 116, 121, 112, 101, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__13_value:
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
        32, 32, 117, 110, 105, 118, 115, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__14_value:
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
        32, 32, 100, 101, 112, 69, 108, 105, 109, 32, 32, 32, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__15_value:
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
        32, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 32, 32, 32, 32, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16_value:
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
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___closed__0_value:
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
    m_fun: l_instToStringBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_RecursorInfo_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___closed__1_value:
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
    m_fun: l_Nat_reprFast as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_RecursorInfo_instToString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___closed__2_value:
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
    m_fun: l_instToStringOption___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_RecursorInfo_instToString___closed__3_value:
    crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_RecursorInfo_instToString___lam__0 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 4,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_RecursorInfo_instToString___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_RecursorInfo_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_RecursorInfo_instToString___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__2_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 105, 115, 82, 101, 99, 63, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__6_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0_value:
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
        105, 110, 118, 97, 108, 105, 100, 32, 117, 115, 101, 114, 32, 100, 101, 102, 105, 110, 101,
        100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 96, 0,
    ],
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2_value:
    crate::leanh::LeanStringObject<129> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 129,
    m_capacity: 129,
    m_length: 128,
    m_data: [
        96, 44, 32, 114, 101, 115, 117, 108, 116, 32, 116, 121, 112, 101, 32, 109, 117, 115, 116,
        32, 98, 101, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 67, 32, 116,
        96, 44, 32, 119, 104, 101, 114, 101, 32, 96, 67, 96, 32, 105, 115, 32, 97, 32, 98, 111,
        117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 44, 32, 97, 110, 100, 32, 116, 32,
        105, 115, 32, 97, 32, 40, 112, 111, 115, 115, 105, 98, 108, 121, 32, 101, 109, 112, 116,
        121, 41, 32, 115, 101, 113, 117, 101, 110, 99, 101, 32, 111, 102, 32, 98, 111, 117, 110,
        100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0,
    ],
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0_value:
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114,
        32, 96, 0,
    ],
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2_value:
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
        105, 110, 118, 97, 108, 105, 100, 32, 117, 115, 101, 114, 32, 100, 101, 102, 105, 110, 101,
        100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 44, 32, 96, 0,
    ],
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4_value:
    crate::leanh::LeanStringObject<191> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 191,
    m_capacity: 191,
    m_length: 190,
    m_data: [
        96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 32,
        100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 101, 108, 105, 109, 105, 110, 97, 116,
        105, 111, 110, 44, 32, 97, 110, 100, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 111,
        102, 32, 116, 104, 101, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101,
        32, 119, 97, 115, 32, 110, 111, 116, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32,
        40, 115, 111, 108, 117, 116, 105, 111, 110, 58, 32, 115, 101, 116, 32, 97, 116, 116, 114,
        105, 98, 117, 116, 101, 32, 96, 91, 114, 101, 99, 117, 114, 115, 111, 114, 32, 60, 112,
        111, 115, 62, 93, 96, 44, 32, 119, 104, 101, 114, 101, 32, 96, 60, 112, 111, 115, 62, 96,
        32, 105, 115, 32, 116, 104, 101, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 102,
        32, 116, 104, 101, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 41,
        0,
    ],
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6_value:
    crate::leanh::LeanStringObject<77> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 77,
    m_capacity: 77,
    m_length: 76,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105,
        115, 101, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 102, 111, 114, 32, 117, 115, 101,
        114, 32, 100, 101, 102, 105, 110, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 44,
        32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 104, 97, 115, 32, 111, 110, 108, 121, 32, 0,
    ],
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8_value:
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
    m_data: [32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 0],
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<69> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [96, 44, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0_value:
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
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<65> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 65, m_capacity: 65, m_length: 64, m_data: [96, 44, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 105, 110, 100, 101, 120, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0_value:
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
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0_value:
    crate::leanh::LeanStringObject<85> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 85,
    m_capacity: 85,
    m_length: 84,
    m_data: [
        96, 44, 32, 109, 111, 116, 105, 118, 101, 32, 114, 101, 115, 117, 108, 116, 32, 115, 111,
        114, 116, 32, 109, 117, 115, 116, 32, 98, 101, 32, 80, 114, 111, 112, 32, 111, 114, 32, 96,
        83, 111, 114, 116, 32, 117, 96, 32, 119, 104, 101, 114, 101, 32, 117, 32, 105, 115, 32, 97,
        32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 112, 97, 114,
        97, 109, 101, 116, 101, 114, 0,
    ],
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<66> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 66, m_capacity: 66, m_length: 65, m_data: [96, 44, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 116, 121, 112, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 96, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0_value:
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
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0_value: crate::leanh::LeanStringObject<219> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 219, m_capacity: 219, m_length: 218, m_data: [96, 44, 32, 109, 111, 116, 105, 118, 101, 32, 109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 97, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 40, 67, 32, 58, 32, 80, 105, 32, 40, 105, 32, 58, 32, 66, 32, 65, 41, 44, 32, 73, 32, 65, 32, 105, 32, 45, 62, 32, 84, 121, 112, 101, 41, 44, 32, 119, 104, 101, 114, 101, 32, 65, 32, 105, 115, 32, 40, 112, 111, 115, 115, 105, 98, 108, 121, 32, 101, 109, 112, 116, 121, 41, 32, 115, 101, 113, 117, 101, 110, 99, 101, 32, 111, 102, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 40, 97, 107, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 41, 44, 32, 40, 105, 32, 58, 32, 66, 32, 65, 41, 32, 105, 115, 32, 97, 32, 40, 112, 111, 115, 115, 105, 98, 108, 121, 32, 101, 109, 112, 116, 121, 41, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 40, 97, 107, 97, 32, 105, 110, 100, 105, 99, 101, 115, 41, 44, 32, 97, 110, 100, 32, 73, 32, 105, 115, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0]};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0_value: crate::leanh::LeanStringObject<80> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 80, m_capacity: 80, m_length: 79, m_data: [96, 44, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 109, 117, 115, 116, 32, 98, 101, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 40, 73, 32, 46, 46, 46, 41, 44, 32, 119, 104, 101, 114, 101, 32, 73, 32, 105, 115, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0]};
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 44, 32, 105, 110, 100, 105, 99, 101, 115, 32, 109, 117, 115, 116, 32, 111, 99, 99, 117, 114, 32, 98, 101, 102, 111, 114, 101, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 0]};
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0_value:
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
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1_value:
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
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2_value:
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
    m_data: [65, 116, 116, 114, 0],
};
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3_value:
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
    m_data: [114, 101, 99, 117, 114, 115, 111, 114, 0],
};
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2_value)
            as *mut crate::leanh::LeanObject,
        4584992172905639687 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3_value)
            as *mut crate::leanh::LeanObject,
        6133751819545484634 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5_value:
    crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116,
        101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 44, 32, 110, 117, 109, 101, 114, 97, 108,
        32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 112, 111, 115, 105, 116,
        105, 111, 110, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 114, 101, 97, 116, 101, 114,
        32, 116, 104, 97, 110, 32, 122, 101, 114, 111, 0,
    ],
};
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut crate::leanh::LeanObject,72621647814721793 as *mut crate::leanh::LeanObject,65793 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 99, 117, 114, 115, 111, 114, 65, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5446437284506570309 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3_value) as *mut crate::leanh::LeanObject,1767031721345221094 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<83> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [117, 115, 101, 114, 32, 100, 101, 102, 105, 110, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 44, 32, 110, 117, 109, 101, 114, 105, 99, 97, 108, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 115, 112, 101, 99, 105, 102, 105, 101, 115, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 111, 102, 32, 116, 104, 101, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 0]};
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 8) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_recursorAttribute: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_RecursorUnivLevelPos_ctorIdx(
    mut v_x_2741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2741_) == 0 {
        let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2742_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2742_;
    } else {
        let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2743_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2743_;
    }
}
pub unsafe fn l_Lean_Meta_RecursorUnivLevelPos_ctorIdx___boxed(
    mut v_x_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2745_ = l_Lean_Meta_RecursorUnivLevelPos_ctorIdx(v_x_2744_);
    crate::leanh::lean_dec(v_x_2744_);
    return v_res_2745_;
}
pub unsafe fn l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(
    mut v_t_2746_: *mut crate::leanh::LeanObject,
    mut v_k_2747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2746_) == 0 {
        return v_k_2747_;
    } else {
        let mut v_idx_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_idx_2748_ = crate::leanh::lean_ctor_get(v_t_2746_, 0);
        crate::leanh::lean_inc(v_idx_2748_);
        crate::leanh::lean_dec_ref_known(v_t_2746_, 1);
        v___x_2749_ = crate::leanh::lean_apply_1(v_k_2747_, v_idx_2748_);
        return v___x_2749_;
    }
}
pub unsafe fn l_Lean_Meta_RecursorUnivLevelPos_ctorElim(
    mut v_motive_2750_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2751_: *mut crate::leanh::LeanObject,
    mut v_t_2752_: *mut crate::leanh::LeanObject,
    mut v_h_2753_: *mut crate::leanh::LeanObject,
    mut v_k_2754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2755_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_2752_, v_k_2754_);
    return v___x_2755_;
}
pub unsafe fn l_Lean_Meta_RecursorUnivLevelPos_ctorElim___boxed(
    mut v_motive_2756_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2757_: *mut crate::leanh::LeanObject,
    mut v_t_2758_: *mut crate::leanh::LeanObject,
    mut v_h_2759_: *mut crate::leanh::LeanObject,
    mut v_k_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim(
        v_motive_2756_,
        v_ctorIdx_2757_,
        v_t_2758_,
        v_h_2759_,
        v_k_2760_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2757_);
    return v_res_2761_;
}
pub unsafe fn l_Lean_Meta_RecursorUnivLevelPos_motive_elim___redArg(
    mut v_t_2762_: *mut crate::leanh::LeanObject,
    mut v_motive_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_2762_, v_motive_2763_);
    return v___x_2764_;
}
pub unsafe fn l_Lean_Meta_RecursorUnivLevelPos_motive_elim(
    mut v_motive_2765_: *mut crate::leanh::LeanObject,
    mut v_t_2766_: *mut crate::leanh::LeanObject,
    mut v_h_2767_: *mut crate::leanh::LeanObject,
    mut v_motive_2768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2769_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_2766_, v_motive_2768_);
    return v___x_2769_;
}
pub unsafe fn l_Lean_Meta_RecursorUnivLevelPos_majorType_elim___redArg(
    mut v_t_2770_: *mut crate::leanh::LeanObject,
    mut v_majorType_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2772_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_2770_, v_majorType_2771_);
    return v___x_2772_;
}
pub unsafe fn l_Lean_Meta_RecursorUnivLevelPos_majorType_elim(
    mut v_motive_2773_: *mut crate::leanh::LeanObject,
    mut v_t_2774_: *mut crate::leanh::LeanObject,
    mut v_h_2775_: *mut crate::leanh::LeanObject,
    mut v_majorType_2776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2777_ = l_Lean_Meta_RecursorUnivLevelPos_ctorElim___redArg(v_t_2774_, v_majorType_2776_);
    return v___x_2777_;
}
pub unsafe fn l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0(
    mut v_x_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2779_) == 0 {
        let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2780_ = l_Lean_Meta_instToStringRecursorUnivLevelPos___lam__0___closed__0;
        return v___x_2780_;
    } else {
        let mut v_idx_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_idx_2781_ = crate::leanh::lean_ctor_get(v_x_2779_, 0);
        crate::leanh::lean_inc(v_idx_2781_);
        crate::leanh::lean_dec_ref_known(v_x_2779_, 1);
        v___x_2782_ = l_Nat_reprFast(v_idx_2781_);
        return v___x_2782_;
    }
}
pub unsafe fn l_Lean_Meta_RecursorInfo_numParams(
    mut v_info_2785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_paramsPos_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_paramsPos_2786_ = crate::leanh::lean_ctor_get(v_info_2785_, 5);
    v___x_2787_ = l_List_lengthTR___redArg(v_paramsPos_2786_);
    return v___x_2787_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_numParams___boxed(
    mut v_info_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2789_ = l_Lean_Meta_RecursorInfo_numParams(v_info_2788_);
    crate::leanh::lean_dec_ref(v_info_2788_);
    return v_res_2789_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_numIndices(
    mut v_info_2790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_indicesPos_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_indicesPos_2791_ = crate::leanh::lean_ctor_get(v_info_2790_, 6);
    v___x_2792_ = l_List_lengthTR___redArg(v_indicesPos_2791_);
    return v___x_2792_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_numIndices___boxed(
    mut v_info_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2794_ = l_Lean_Meta_RecursorInfo_numIndices(v_info_2793_);
    crate::leanh::lean_dec_ref(v_info_2793_);
    return v_res_2794_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_motivePos(
    mut v_info_2795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2796_ = l_Lean_Meta_RecursorInfo_numParams(v_info_2795_);
    return v___x_2796_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_motivePos___boxed(
    mut v_info_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Lean_Meta_RecursorInfo_motivePos(v_info_2797_);
    crate::leanh::lean_dec_ref(v_info_2797_);
    return v_res_2798_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_firstIndexPos(
    mut v_info_2799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_majorPos_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_majorPos_2800_ = crate::leanh::lean_ctor_get(v_info_2799_, 4);
    v___x_2801_ = l_Lean_Meta_RecursorInfo_numIndices(v_info_2799_);
    v___x_2802_ = lean_nat_sub(v_majorPos_2800_, v___x_2801_);
    crate::leanh::lean_dec(v___x_2801_);
    return v___x_2802_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(
    mut v_info_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2804_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_info_2803_);
    crate::leanh::lean_dec_ref(v_info_2803_);
    return v_res_2804_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_isMinor(
    mut v_info_2805_: *mut crate::leanh::LeanObject,
    mut v_pos_2806_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___y_2810_: u8 = 0;
    let mut v___x_2811_: u8 = 0;
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: u8 = 0;
    let mut v_majorPos_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2807_ = l_Lean_Meta_RecursorInfo_numParams(v_info_2805_);
                v___x_2808_ = lean_nat_dec_le(v_pos_2806_, v___x_2807_);
                crate::leanh::lean_dec(v___x_2807_);
                if v___x_2808_ == 0 {
                    v___x_2812_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_info_2805_);
                    v___x_2813_ = lean_nat_dec_le(v___x_2812_, v_pos_2806_);
                    crate::leanh::lean_dec(v___x_2812_);
                    if v___x_2813_ == 0 {
                        v___y_2810_ = v___x_2813_;
                        state = 1;
                        continue;
                    } else {
                        v_majorPos_2814_ = crate::leanh::lean_ctor_get(v_info_2805_, 4);
                        v___x_2815_ = lean_nat_dec_le(v_pos_2806_, v_majorPos_2814_);
                        v___y_2810_ = v___x_2815_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2816_ = 0;
                    return v___x_2816_;
                }
            }
            1 => {
                if v___y_2810_ == 0 {
                    v___x_2811_ = 1;
                    return v___x_2811_;
                } else {
                    return v___x_2808_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_RecursorInfo_isMinor___boxed(
    mut v_info_2817_: *mut crate::leanh::LeanObject,
    mut v_pos_2818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2819_: u8 = 0;
    let mut v_r_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2819_ = l_Lean_Meta_RecursorInfo_isMinor(v_info_2817_, v_pos_2818_);
    crate::leanh::lean_dec(v_pos_2818_);
    crate::leanh::lean_dec_ref(v_info_2817_);
    v_r_2820_ = crate::leanh::lean_box((v_res_2819_) as usize);
    return v_r_2820_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_numMinors(
    mut v_info_2821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numArgs_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_majorPos_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_numArgs_2822_ = crate::leanh::lean_ctor_get(v_info_2821_, 3);
    v_majorPos_2823_ = crate::leanh::lean_ctor_get(v_info_2821_, 4);
    v___x_2824_ = l_Lean_Meta_RecursorInfo_numParams(v_info_2821_);
    v___x_2825_ = lean_nat_sub(v_numArgs_2822_, v___x_2824_);
    crate::leanh::lean_dec(v___x_2824_);
    v___x_2826_ = crate::leanh::lean_unsigned_to_nat(1);
    v_r_2827_ = lean_nat_sub(v___x_2825_, v___x_2826_);
    crate::leanh::lean_dec(v___x_2825_);
    v___x_2828_ = lean_nat_add(v_majorPos_2823_, v___x_2826_);
    v___x_2829_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_info_2821_);
    v___x_2830_ = lean_nat_sub(v___x_2828_, v___x_2829_);
    crate::leanh::lean_dec(v___x_2829_);
    crate::leanh::lean_dec(v___x_2828_);
    v___x_2831_ = lean_nat_sub(v_r_2827_, v___x_2830_);
    crate::leanh::lean_dec(v___x_2830_);
    crate::leanh::lean_dec(v_r_2827_);
    return v___x_2831_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_numMinors___boxed(
    mut v_info_2832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2833_ = l_Lean_Meta_RecursorInfo_numMinors(v_info_2832_);
    crate::leanh::lean_dec_ref(v_info_2832_);
    return v_res_2833_;
}
pub unsafe fn l_Lean_Meta_RecursorInfo_instToString___lam__0(
    mut v___f_2852_: *mut crate::leanh::LeanObject,
    mut v___f_2853_: *mut crate::leanh::LeanObject,
    mut v___f_2854_: *mut crate::leanh::LeanObject,
    mut v___f_2855_: *mut crate::leanh::LeanObject,
    mut v_info_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_recursorName_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univLevelPos_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depElim_2860_: u8 = 0;
    let mut v_recursive_2861_: u8 = 0;
    let mut v_numArgs_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_majorPos_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPos_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_produceMotive_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_recursorName_2857_ = crate::leanh::lean_ctor_get(v_info_2856_, 0);
                v_typeName_2858_ = crate::leanh::lean_ctor_get(v_info_2856_, 1);
                v_univLevelPos_2859_ = crate::leanh::lean_ctor_get(v_info_2856_, 2);
                v_depElim_2860_ = crate::leanh::lean_ctor_get_uint8(
                    v_info_2856_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                v_recursive_2861_ = crate::leanh::lean_ctor_get_uint8(
                    v_info_2856_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_numArgs_2862_ = crate::leanh::lean_ctor_get(v_info_2856_, 3);
                v_majorPos_2863_ = crate::leanh::lean_ctor_get(v_info_2856_, 4);
                crate::leanh::lean_inc(v_majorPos_2863_);
                v_paramsPos_2864_ = crate::leanh::lean_ctor_get(v_info_2856_, 5);
                crate::leanh::lean_inc(v_paramsPos_2864_);
                v_indicesPos_2865_ = crate::leanh::lean_ctor_get(v_info_2856_, 6);
                crate::leanh::lean_inc(v_indicesPos_2865_);
                v_produceMotive_2866_ = crate::leanh::lean_ctor_get(v_info_2856_, 7);
                crate::leanh::lean_inc(v_produceMotive_2866_);
                v___x_2867_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__0;
                v___x_2868_ = 1;
                crate::leanh::lean_inc(v_recursorName_2857_);
                v___x_2869_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_recursorName_2857_,
                    v___x_2868_,
                );
                v___x_2870_ = lean_string_append(v___x_2867_, v___x_2869_);
                crate::leanh::lean_dec_ref(v___x_2869_);
                v___x_2871_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__1;
                v___x_2926_ = lean_string_append(v___x_2870_, v___x_2871_);
                v___x_2927_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__12;
                v___x_2928_ = lean_string_append(v___x_2926_, v___x_2927_);
                crate::leanh::lean_inc(v_typeName_2858_);
                v___x_2929_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_typeName_2858_,
                    v___x_2868_,
                );
                v___x_2930_ = lean_string_append(v___x_2928_, v___x_2929_);
                crate::leanh::lean_dec_ref(v___x_2929_);
                v___x_2931_ = lean_string_append(v___x_2930_, v___x_2871_);
                v___x_2932_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__13;
                v___x_2933_ = lean_string_append(v___x_2931_, v___x_2932_);
                crate::leanh::lean_inc(v_univLevelPos_2859_);
                v___x_2934_ = l_List_toString___redArg(v___f_2855_, v_univLevelPos_2859_);
                v___x_2935_ = lean_string_append(v___x_2933_, v___x_2934_);
                crate::leanh::lean_dec_ref(v___x_2934_);
                v___x_2936_ = lean_string_append(v___x_2935_, v___x_2871_);
                v___x_2937_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__14;
                v___x_2938_ = lean_string_append(v___x_2936_, v___x_2937_);
                if v_depElim_2860_ == 0 {
                    v___x_2947_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16;
                    v___y_2940_ = v___x_2947_;
                    state = 2;
                    continue;
                } else {
                    v___x_2948_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17;
                    v___y_2940_ = v___x_2948_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2875_ = lean_string_append(v___y_2873_, v___y_2874_);
                v___x_2876_ = lean_string_append(v___x_2875_, v___x_2871_);
                v___x_2877_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__2;
                v___x_2878_ = lean_string_append(v___x_2876_, v___x_2877_);
                crate::leanh::lean_inc(v_numArgs_2862_);
                v___x_2879_ = l_Nat_reprFast(v_numArgs_2862_);
                v___x_2880_ = lean_string_append(v___x_2878_, v___x_2879_);
                crate::leanh::lean_dec_ref(v___x_2879_);
                v___x_2881_ = lean_string_append(v___x_2880_, v___x_2871_);
                v___x_2882_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__3;
                v___x_2883_ = lean_string_append(v___x_2881_, v___x_2882_);
                v___x_2884_ = l_Lean_Meta_RecursorInfo_numParams(v_info_2856_);
                v___x_2885_ = l_Nat_reprFast(v___x_2884_);
                v___x_2886_ = lean_string_append(v___x_2883_, v___x_2885_);
                v___x_2887_ = lean_string_append(v___x_2886_, v___x_2871_);
                v___x_2888_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__4;
                v___x_2889_ = lean_string_append(v___x_2887_, v___x_2888_);
                v___x_2890_ = l_Lean_Meta_RecursorInfo_numIndices(v_info_2856_);
                v___x_2891_ = l_Nat_reprFast(v___x_2890_);
                v___x_2892_ = lean_string_append(v___x_2889_, v___x_2891_);
                crate::leanh::lean_dec_ref(v___x_2891_);
                v___x_2893_ = lean_string_append(v___x_2892_, v___x_2871_);
                v___x_2894_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__5;
                v___x_2895_ = lean_string_append(v___x_2893_, v___x_2894_);
                v___x_2896_ = l_Lean_Meta_RecursorInfo_numMinors(v_info_2856_);
                crate::leanh::lean_dec_ref(v_info_2856_);
                v___x_2897_ = l_Nat_reprFast(v___x_2896_);
                v___x_2898_ = lean_string_append(v___x_2895_, v___x_2897_);
                crate::leanh::lean_dec_ref(v___x_2897_);
                v___x_2899_ = lean_string_append(v___x_2898_, v___x_2871_);
                v___x_2900_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__6;
                v___x_2901_ = lean_string_append(v___x_2899_, v___x_2900_);
                v___x_2902_ = l_Nat_reprFast(v_majorPos_2863_);
                v___x_2903_ = lean_string_append(v___x_2901_, v___x_2902_);
                crate::leanh::lean_dec_ref(v___x_2902_);
                v___x_2904_ = lean_string_append(v___x_2903_, v___x_2871_);
                v___x_2905_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__7;
                v___x_2906_ = lean_string_append(v___x_2904_, v___x_2905_);
                v___x_2907_ = lean_string_append(v___x_2906_, v___x_2885_);
                crate::leanh::lean_dec_ref(v___x_2885_);
                v___x_2908_ = lean_string_append(v___x_2907_, v___x_2871_);
                v___x_2909_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__8;
                v___x_2910_ = lean_string_append(v___x_2908_, v___x_2909_);
                v___x_2911_ = l_List_toString___redArg(v___f_2852_, v_paramsPos_2864_);
                v___x_2912_ = lean_string_append(v___x_2910_, v___x_2911_);
                crate::leanh::lean_dec_ref(v___x_2911_);
                v___x_2913_ = lean_string_append(v___x_2912_, v___x_2871_);
                v___x_2914_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__9;
                v___x_2915_ = lean_string_append(v___x_2913_, v___x_2914_);
                v___x_2916_ = l_List_toString___redArg(v___f_2853_, v_indicesPos_2865_);
                v___x_2917_ = lean_string_append(v___x_2915_, v___x_2916_);
                crate::leanh::lean_dec_ref(v___x_2916_);
                v___x_2918_ = lean_string_append(v___x_2917_, v___x_2871_);
                v___x_2919_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__10;
                v___x_2920_ = lean_string_append(v___x_2918_, v___x_2919_);
                v___x_2921_ = l_List_toString___redArg(v___f_2854_, v_produceMotive_2866_);
                v___x_2922_ = lean_string_append(v___x_2920_, v___x_2921_);
                crate::leanh::lean_dec_ref(v___x_2921_);
                v___x_2923_ = lean_string_append(v___x_2922_, v___x_2871_);
                v___x_2924_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__11;
                v___x_2925_ = lean_string_append(v___x_2923_, v___x_2924_);
                return v___x_2925_;
            }
            2 => {
                v___x_2941_ = lean_string_append(v___x_2938_, v___y_2940_);
                v___x_2942_ = lean_string_append(v___x_2941_, v___x_2871_);
                v___x_2943_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__15;
                v___x_2944_ = lean_string_append(v___x_2942_, v___x_2943_);
                if v_recursive_2861_ == 0 {
                    v___x_2945_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__16;
                    v___y_2873_ = v___x_2944_;
                    v___y_2874_ = v___x_2945_;
                    state = 1;
                    continue;
                } else {
                    v___x_2946_ = l_Lean_Meta_RecursorInfo_instToString___lam__0___closed__17;
                    v___y_2873_ = v___x_2944_;
                    v___y_2874_ = v___x_2946_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2959_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(
    mut v_msg_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
    mut v___y_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2975_: u8 = 0;
    let mut v_toFunctor_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2982_: u8 = 0;
    let mut v___f_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2999_: u8 = 0;
    let mut v_toFunctor_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___f_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473__overap_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3025_: u8 = 0;
    let mut v_unused_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3027_: u8 = 0;
    let mut v_unused_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3031_: u8 = 0;
    let mut v_unused_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3033_: u8 = 0;
    let mut v_unused_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2970_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__0);
                v___x_2971_ = l_StateRefT_x27_instMonad___redArg(v___x_2970_);
                v_toApplicative_2972_ = crate::leanh::lean_ctor_get(v___x_2971_, 0);
                v_isSharedCheck_3033_ = (!crate::leanh::lean_is_exclusive(v___x_2971_)) as u8;
                if v_isSharedCheck_3033_ == 0 {
                    v_unused_3034_ = crate::leanh::lean_ctor_get(v___x_2971_, 1);
                    crate::leanh::lean_dec(v_unused_3034_);
                    v___x_2974_ = v___x_2971_;
                    v_isShared_2975_ = v_isSharedCheck_3033_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2972_);
                    crate::leanh::lean_dec(v___x_2971_);
                    v___x_2974_ = crate::leanh::lean_box(0);
                    v_isShared_2975_ = v_isSharedCheck_3033_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2976_ = crate::leanh::lean_ctor_get(v_toApplicative_2972_, 0);
                v_toSeq_2977_ = crate::leanh::lean_ctor_get(v_toApplicative_2972_, 2);
                v_toSeqLeft_2978_ = crate::leanh::lean_ctor_get(v_toApplicative_2972_, 3);
                v_toSeqRight_2979_ = crate::leanh::lean_ctor_get(v_toApplicative_2972_, 4);
                v_isSharedCheck_3031_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2972_)) as u8;
                if v_isSharedCheck_3031_ == 0 {
                    v_unused_3032_ = crate::leanh::lean_ctor_get(v_toApplicative_2972_, 1);
                    crate::leanh::lean_dec(v_unused_3032_);
                    v___x_2981_ = v_toApplicative_2972_;
                    v_isShared_2982_ = v_isSharedCheck_3031_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2979_);
                    crate::leanh::lean_inc(v_toSeqLeft_2978_);
                    crate::leanh::lean_inc(v_toSeq_2977_);
                    crate::leanh::lean_inc(v_toFunctor_2976_);
                    crate::leanh::lean_dec(v_toApplicative_2972_);
                    v___x_2981_ = crate::leanh::lean_box(0);
                    v_isShared_2982_ = v_isSharedCheck_3031_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2983_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__1;
                v___f_2984_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2976_);
                v___f_2985_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2985_, 0, v_toFunctor_2976_);
                v___f_2986_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2986_, 0, v_toFunctor_2976_);
                v___x_2987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2987_, 0, v___f_2985_);
                crate::leanh::lean_ctor_set(v___x_2987_, 1, v___f_2986_);
                v___f_2988_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2988_, 0, v_toSeqRight_2979_);
                v___f_2989_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2989_, 0, v_toSeqLeft_2978_);
                v___f_2990_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2990_, 0, v_toSeq_2977_);
                if v_isShared_2982_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2981_, 4, v___f_2988_);
                    crate::leanh::lean_ctor_set(v___x_2981_, 3, v___f_2989_);
                    crate::leanh::lean_ctor_set(v___x_2981_, 2, v___f_2990_);
                    crate::leanh::lean_ctor_set(v___x_2981_, 1, v___f_2983_);
                    crate::leanh::lean_ctor_set(v___x_2981_, 0, v___x_2987_);
                    v___x_2992_ = v___x_2981_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3030_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_2987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___f_2983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 2, v___f_2990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 3, v___f_2989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 4, v___f_2988_);
                    v___x_2992_ = v_reuseFailAlloc_3030_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2975_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2974_, 1, v___f_2984_);
                    crate::leanh::lean_ctor_set(v___x_2974_, 0, v___x_2992_);
                    v___x_2994_ = v___x_2974_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3029_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_2992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___f_2984_);
                    v___x_2994_ = v_reuseFailAlloc_3029_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2995_ = l_StateRefT_x27_instMonad___redArg(v___x_2994_);
                v_toApplicative_2996_ = crate::leanh::lean_ctor_get(v___x_2995_, 0);
                v_isSharedCheck_3027_ = (!crate::leanh::lean_is_exclusive(v___x_2995_)) as u8;
                if v_isSharedCheck_3027_ == 0 {
                    v_unused_3028_ = crate::leanh::lean_ctor_get(v___x_2995_, 1);
                    crate::leanh::lean_dec(v_unused_3028_);
                    v___x_2998_ = v___x_2995_;
                    v_isShared_2999_ = v_isSharedCheck_3027_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2996_);
                    crate::leanh::lean_dec(v___x_2995_);
                    v___x_2998_ = crate::leanh::lean_box(0);
                    v_isShared_2999_ = v_isSharedCheck_3027_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3000_ = crate::leanh::lean_ctor_get(v_toApplicative_2996_, 0);
                v_toSeq_3001_ = crate::leanh::lean_ctor_get(v_toApplicative_2996_, 2);
                v_toSeqLeft_3002_ = crate::leanh::lean_ctor_get(v_toApplicative_2996_, 3);
                v_toSeqRight_3003_ = crate::leanh::lean_ctor_get(v_toApplicative_2996_, 4);
                v_isSharedCheck_3025_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2996_)) as u8;
                if v_isSharedCheck_3025_ == 0 {
                    v_unused_3026_ = crate::leanh::lean_ctor_get(v_toApplicative_2996_, 1);
                    crate::leanh::lean_dec(v_unused_3026_);
                    v___x_3005_ = v_toApplicative_2996_;
                    v_isShared_3006_ = v_isSharedCheck_3025_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3003_);
                    crate::leanh::lean_inc(v_toSeqLeft_3002_);
                    crate::leanh::lean_inc(v_toSeq_3001_);
                    crate::leanh::lean_inc(v_toFunctor_3000_);
                    crate::leanh::lean_dec(v_toApplicative_2996_);
                    v___x_3005_ = crate::leanh::lean_box(0);
                    v_isShared_3006_ = v_isSharedCheck_3025_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3007_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__3;
                v___f_3008_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_3000_);
                v___f_3009_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3009_, 0, v_toFunctor_3000_);
                v___f_3010_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3010_, 0, v_toFunctor_3000_);
                v___x_3011_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3011_, 0, v___f_3009_);
                crate::leanh::lean_ctor_set(v___x_3011_, 1, v___f_3010_);
                v___f_3012_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3012_, 0, v_toSeqRight_3003_);
                v___f_3013_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3013_, 0, v_toSeqLeft_3002_);
                v___f_3014_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3014_, 0, v_toSeq_3001_);
                if v_isShared_3006_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3005_, 4, v___f_3012_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 3, v___f_3013_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 2, v___f_3014_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 1, v___f_3007_);
                    crate::leanh::lean_ctor_set(v___x_3005_, 0, v___x_3011_);
                    v___x_3016_ = v___x_3005_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3024_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___f_3007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3024_, 2, v___f_3014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3024_, 3, v___f_3013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3024_, 4, v___f_3012_);
                    v___x_3016_ = v_reuseFailAlloc_3024_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2998_, 1, v___f_3008_);
                    crate::leanh::lean_ctor_set(v___x_2998_, 0, v___x_3016_);
                    v___x_3018_ = v___x_2998_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3023_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3023_, 1, v___f_3008_);
                    v___x_3018_ = v_reuseFailAlloc_3023_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3019_ = crate::leanh::lean_box(0);
                v___x_3020_ = l_instInhabitedOfMonad___redArg(v___x_3018_, v___x_3019_);
                v___x_3473__overap_3021_ = lean_panic_fn_borrowed(v___x_3020_, v_msg_2964_);
                crate::leanh::lean_dec(v___x_3020_);
                crate::leanh::lean_inc(v___y_2968_);
                crate::leanh::lean_inc_ref(v___y_2967_);
                crate::leanh::lean_inc(v___y_2966_);
                crate::leanh::lean_inc_ref(v___y_2965_);
                v___x_3022_ = crate::leanh::lean_apply_5(
                    v___x_3473__overap_3021_,
                    v___y_2965_,
                    v___y_2966_,
                    v___y_2967_,
                    v___y_2968_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3022_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1___boxed(
    mut v_msg_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
    mut v___y_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3041_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(v_msg_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
    crate::leanh::lean_dec(v___y_3039_);
    crate::leanh::lean_dec_ref(v___y_3038_);
    crate::leanh::lean_dec(v___y_3037_);
    crate::leanh::lean_dec_ref(v___y_3036_);
    return v_res_3041_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(
    mut v_msgData_3042_: *mut crate::leanh::LeanObject,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
    mut v___y_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = lean_st_ref_get(v___y_3046_);
    v_env_3049_ = crate::leanh::lean_ctor_get(v___x_3048_, 0);
    crate::leanh::lean_inc_ref(v_env_3049_);
    crate::leanh::lean_dec(v___x_3048_);
    v___x_3050_ = lean_st_ref_get(v___y_3044_);
    v_mctx_3051_ = crate::leanh::lean_ctor_get(v___x_3050_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3051_);
    crate::leanh::lean_dec(v___x_3050_);
    v_lctx_3052_ = crate::leanh::lean_ctor_get(v___y_3043_, 2);
    v_options_3053_ = crate::leanh::lean_ctor_get(v___y_3045_, 2);
    crate::leanh::lean_inc_ref(v_options_3053_);
    crate::leanh::lean_inc_ref(v_lctx_3052_);
    v___x_3054_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3054_, 0, v_env_3049_);
    crate::leanh::lean_ctor_set(v___x_3054_, 1, v_mctx_3051_);
    crate::leanh::lean_ctor_set(v___x_3054_, 2, v_lctx_3052_);
    crate::leanh::lean_ctor_set(v___x_3054_, 3, v_options_3053_);
    v___x_3055_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3055_, 0, v___x_3054_);
    crate::leanh::lean_ctor_set(v___x_3055_, 1, v_msgData_3042_);
    v___x_3056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3056_, 0, v___x_3055_);
    return v___x_3056_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_3057_: *mut crate::leanh::LeanObject,
    mut v___y_3058_: *mut crate::leanh::LeanObject,
    mut v___y_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3063_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(v_msgData_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
    crate::leanh::lean_dec(v___y_3061_);
    crate::leanh::lean_dec_ref(v___y_3060_);
    crate::leanh::lean_dec(v___y_3059_);
    crate::leanh::lean_dec_ref(v___y_3058_);
    return v_res_3063_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(
    mut v_msg_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
    mut v___y_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
    mut v___y_3068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3075_: u8 = 0;
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3070_ = crate::leanh::lean_ctor_get(v___y_3067_, 5);
                v___x_3071_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0_spec__1(v_msg_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
                v_a_3072_ = crate::leanh::lean_ctor_get(v___x_3071_, 0);
                v_isSharedCheck_3080_ = (!crate::leanh::lean_is_exclusive(v___x_3071_)) as u8;
                if v_isSharedCheck_3080_ == 0 {
                    v___x_3074_ = v___x_3071_;
                    v_isShared_3075_ = v_isSharedCheck_3080_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3072_);
                    crate::leanh::lean_dec(v___x_3071_);
                    v___x_3074_ = crate::leanh::lean_box(0);
                    v_isShared_3075_ = v_isSharedCheck_3080_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3070_);
                v___x_3076_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3076_, 0, v_ref_3070_);
                crate::leanh::lean_ctor_set(v___x_3076_, 1, v_a_3072_);
                if v_isShared_3075_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3074_, 1);
                    crate::leanh::lean_ctor_set(v___x_3074_, 0, v___x_3076_);
                    v___x_3078_ = v___x_3074_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
                    v___x_3078_ = v_reuseFailAlloc_3079_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3078_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg___boxed(
    mut v_msg_3081_: *mut crate::leanh::LeanObject,
    mut v___y_3082_: *mut crate::leanh::LeanObject,
    mut v___y_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
    mut v___y_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
    crate::leanh::lean_dec(v___y_3085_);
    crate::leanh::lean_dec_ref(v___y_3084_);
    crate::leanh::lean_dec(v___y_3083_);
    crate::leanh::lean_dec_ref(v___y_3082_);
    return v_res_3087_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3089_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__0;
    v___x_3090_ = l_Lean_stringToMessageData(v___x_3089_);
    return v___x_3090_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3092_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__2;
    v___x_3093_ = l_Lean_stringToMessageData(v___x_3092_);
    return v___x_3093_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3097_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__6;
    v___x_3098_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_3099_ = crate::leanh::lean_unsigned_to_nat(129);
    v___x_3100_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__5;
    v___x_3101_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__4;
    v___x_3102_ = l_mkPanicMessageWithDecl(
        v___x_3101_,
        v___x_3100_,
        v___x_3099_,
        v___x_3098_,
        v___x_3097_,
    );
    return v___x_3102_;
}
pub unsafe fn l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(
    mut v_constName_3103_: *mut crate::leanh::LeanObject,
    mut v___y_3104_: *mut crate::leanh::LeanObject,
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: u8 = 0;
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3122_: u8 = 0;
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3131_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3137_: u8 = 0;
    let mut v_val_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v_a_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3146_: u8 = 0;
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3117_ = lean_st_ref_get(v___y_3107_);
                v_env_3118_ = crate::leanh::lean_ctor_get(v___x_3117_, 0);
                crate::leanh::lean_inc_ref(v_env_3118_);
                crate::leanh::lean_dec(v___x_3117_);
                v___x_3119_ = 0;
                crate::leanh::lean_inc(v_constName_3103_);
                v___x_3120_ =
                    l_Lean_Environment_findAsync_x3f(v_env_3118_, v_constName_3103_, v___x_3119_);
                if crate::leanh::lean_obj_tag(v___x_3120_) == 1 {
                    v_val_3121_ = crate::leanh::lean_ctor_get(v___x_3120_, 0);
                    crate::leanh::lean_inc(v_val_3121_);
                    crate::leanh::lean_dec_ref_known(v___x_3120_, 1);
                    v_kind_3122_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_3121_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_3122_ == 7 {
                        v___x_3123_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_3121_);
                        if crate::leanh::lean_obj_tag(v___x_3123_) == 7 {
                            crate::leanh::lean_dec(v_constName_3103_);
                            v_val_3124_ = crate::leanh::lean_ctor_get(v___x_3123_, 0);
                            v_isSharedCheck_3131_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3123_)) as u8;
                            if v_isSharedCheck_3131_ == 0 {
                                v___x_3126_ = v___x_3123_;
                                v_isShared_3127_ = v_isSharedCheck_3131_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_3124_);
                                crate::leanh::lean_dec(v___x_3123_);
                                v___x_3126_ = crate::leanh::lean_box(0);
                                v_isShared_3127_ = v_isSharedCheck_3131_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3123_);
                            v___x_3132_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__7);
                            v___x_3133_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__1(v___x_3132_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
                            if crate::leanh::lean_obj_tag(v___x_3133_) == 0 {
                                v_a_3134_ = crate::leanh::lean_ctor_get(v___x_3133_, 0);
                                v_isSharedCheck_3142_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3133_)) as u8;
                                if v_isSharedCheck_3142_ == 0 {
                                    v___x_3136_ = v___x_3133_;
                                    v_isShared_3137_ = v_isSharedCheck_3142_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3134_);
                                    crate::leanh::lean_dec(v___x_3133_);
                                    v___x_3136_ = crate::leanh::lean_box(0);
                                    v_isShared_3137_ = v_isSharedCheck_3142_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_3103_);
                                v_a_3143_ = crate::leanh::lean_ctor_get(v___x_3133_, 0);
                                v_isSharedCheck_3150_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3133_)) as u8;
                                if v_isSharedCheck_3150_ == 0 {
                                    v___x_3145_ = v___x_3133_;
                                    v_isShared_3146_ = v_isSharedCheck_3150_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3143_);
                                    crate::leanh::lean_dec(v___x_3133_);
                                    v___x_3145_ = crate::leanh::lean_box(0);
                                    v_isShared_3146_ = v_isSharedCheck_3150_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3121_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3120_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3110_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
                v___x_3111_ = 0;
                v___x_3112_ = l_Lean_MessageData_ofConstName(v_constName_3103_, v___x_3111_);
                v___x_3113_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3113_, 0, v___x_3110_);
                crate::leanh::lean_ctor_set(v___x_3113_, 1, v___x_3112_);
                v___x_3114_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__3);
                v___x_3115_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3115_, 0, v___x_3113_);
                crate::leanh::lean_ctor_set(v___x_3115_, 1, v___x_3114_);
                v___x_3116_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_3115_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
                return v___x_3116_;
            }
            2 => {
                if v_isShared_3127_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3126_, 0);
                    v___x_3129_ = v___x_3126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_val_3124_);
                    v___x_3129_ = v_reuseFailAlloc_3130_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3129_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_3134_) == 0 {
                    crate::leanh::lean_del_object(v___x_3136_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_3103_);
                    v_val_3138_ = crate::leanh::lean_ctor_get(v_a_3134_, 0);
                    crate::leanh::lean_inc(v_val_3138_);
                    crate::leanh::lean_dec_ref_known(v_a_3134_, 1);
                    if v_isShared_3137_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3136_, 0, v_val_3138_);
                        v___x_3140_ = v___x_3136_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_val_3138_);
                        v___x_3140_ = v_reuseFailAlloc_3141_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3140_;
            }
            6 => {
                if v_isShared_3146_ == 0 {
                    v___x_3148_ = v___x_3145_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
                    v___x_3148_ = v_reuseFailAlloc_3149_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___boxed(
    mut v_constName_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
    mut v___y_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3157_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(v_constName_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
    crate::leanh::lean_dec(v___y_3155_);
    crate::leanh::lean_dec_ref(v___y_3154_);
    crate::leanh::lean_dec(v___y_3153_);
    crate::leanh::lean_dec_ref(v___y_3152_);
    return v_res_3157_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(
    mut v_declName_3158_: *mut crate::leanh::LeanObject,
    mut v_majorPos_x3f_3159_: *mut crate::leanh::LeanObject,
    mut v_a_3160_: *mut crate::leanh::LeanObject,
    mut v_a_3161_: *mut crate::leanh::LeanObject,
    mut v_a_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMotives_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_majorPos_x3f_3159_) == 0 {
                    v___x_3171_ = lean_st_ref_get(v_a_3163_);
                    v_env_3172_ = crate::leanh::lean_ctor_get(v___x_3171_, 0);
                    crate::leanh::lean_inc_ref(v_env_3172_);
                    crate::leanh::lean_dec(v___x_3171_);
                    crate::leanh::lean_inc(v_declName_3158_);
                    v___x_3173_ = l_Lean_isAuxRecursor(v_env_3172_, v_declName_3158_);
                    if v___x_3173_ == 0 {
                        crate::leanh::lean_dec(v_declName_3158_);
                        v___x_3174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3174_, 0, v_majorPos_x3f_3159_);
                        return v___x_3174_;
                    } else {
                        if crate::leanh::lean_obj_tag(v_declName_3158_) == 1 {
                            v_pre_3175_ = crate::leanh::lean_ctor_get(v_declName_3158_, 0);
                            crate::leanh::lean_inc(v_pre_3175_);
                            v_str_3176_ = crate::leanh::lean_ctor_get(v_declName_3158_, 1);
                            crate::leanh::lean_inc_ref(v_str_3176_);
                            crate::leanh::lean_dec_ref_known(v_declName_3158_, 2);
                            v___x_3196_ = l_Lean_recOnSuffix;
                            v___x_3197_ = lean_string_dec_eq(v_str_3176_, v___x_3196_);
                            if v___x_3197_ == 0 {
                                if v___x_3173_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3198_ = l_Lean_casesOnSuffix;
                                    v___x_3199_ = lean_string_dec_eq(v_str_3176_, v___x_3198_);
                                    if v___x_3199_ == 0 {
                                        v___x_3200_ = l_Lean_brecOnSuffix;
                                        v___x_3201_ = lean_string_dec_eq(v_str_3176_, v___x_3200_);
                                        if v___x_3201_ == 0 {
                                            crate::leanh::lean_dec_ref(v_str_3176_);
                                            crate::leanh::lean_dec(v_pre_3175_);
                                            v___x_3202_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3202_,
                                                0,
                                                v_majorPos_x3f_3159_,
                                            );
                                            return v___x_3202_;
                                        } else {
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_declName_3158_);
                            v___x_3203_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3203_, 0, v_majorPos_x3f_3159_);
                            return v___x_3203_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_3158_);
                    v___x_3204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3204_, 0, v_majorPos_x3f_3159_);
                    return v___x_3204_;
                }
            }
            1 => {
                v___x_3168_ = lean_nat_add(v___y_3166_, v___y_3167_);
                crate::leanh::lean_dec(v___y_3167_);
                crate::leanh::lean_dec(v___y_3166_);
                v___x_3169_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3169_, 0, v___x_3168_);
                v___x_3170_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3170_, 0, v___x_3169_);
                return v___x_3170_;
            }
            2 => {
                v___x_3178_ = l_Lean_mkRecName(v_pre_3175_);
                v___x_3179_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0(v___x_3178_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_);
                if crate::leanh::lean_obj_tag(v___x_3179_) == 0 {
                    v_a_3180_ = crate::leanh::lean_ctor_get(v___x_3179_, 0);
                    crate::leanh::lean_inc(v_a_3180_);
                    crate::leanh::lean_dec_ref_known(v___x_3179_, 1);
                    v_numParams_3181_ = crate::leanh::lean_ctor_get(v_a_3180_, 2);
                    crate::leanh::lean_inc(v_numParams_3181_);
                    v_numIndices_3182_ = crate::leanh::lean_ctor_get(v_a_3180_, 3);
                    crate::leanh::lean_inc(v_numIndices_3182_);
                    v_numMotives_3183_ = crate::leanh::lean_ctor_get(v_a_3180_, 4);
                    crate::leanh::lean_inc(v_numMotives_3183_);
                    crate::leanh::lean_dec(v_a_3180_);
                    v___x_3184_ = lean_nat_add(v_numParams_3181_, v_numIndices_3182_);
                    crate::leanh::lean_dec(v_numIndices_3182_);
                    crate::leanh::lean_dec(v_numParams_3181_);
                    v___x_3185_ = l_Lean_casesOnSuffix;
                    v___x_3186_ = lean_string_dec_eq(v_str_3176_, v___x_3185_);
                    crate::leanh::lean_dec_ref(v_str_3176_);
                    if v___x_3186_ == 0 {
                        v___y_3166_ = v___x_3184_;
                        v___y_3167_ = v_numMotives_3183_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_numMotives_3183_);
                        v___x_3187_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___y_3166_ = v___x_3184_;
                        v___y_3167_ = v___x_3187_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_str_3176_);
                    v_a_3188_ = crate::leanh::lean_ctor_get(v___x_3179_, 0);
                    v_isSharedCheck_3195_ = (!crate::leanh::lean_is_exclusive(v___x_3179_)) as u8;
                    if v_isSharedCheck_3195_ == 0 {
                        v___x_3190_ = v___x_3179_;
                        v_isShared_3191_ = v_isSharedCheck_3195_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3188_);
                        crate::leanh::lean_dec(v___x_3179_);
                        v___x_3190_ = crate::leanh::lean_box(0);
                        v_isShared_3191_ = v_isSharedCheck_3195_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3191_ == 0 {
                    v___x_3193_ = v___x_3190_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
                    v___x_3193_ = v_reuseFailAlloc_3194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___boxed(
    mut v_declName_3205_: *mut crate::leanh::LeanObject,
    mut v_majorPos_x3f_3206_: *mut crate::leanh::LeanObject,
    mut v_a_3207_: *mut crate::leanh::LeanObject,
    mut v_a_3208_: *mut crate::leanh::LeanObject,
    mut v_a_3209_: *mut crate::leanh::LeanObject,
    mut v_a_3210_: *mut crate::leanh::LeanObject,
    mut v_a_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3212_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(
        v_declName_3205_,
        v_majorPos_x3f_3206_,
        v_a_3207_,
        v_a_3208_,
        v_a_3209_,
        v_a_3210_,
    );
    crate::leanh::lean_dec(v_a_3210_);
    crate::leanh::lean_dec_ref(v_a_3209_);
    crate::leanh::lean_dec(v_a_3208_);
    crate::leanh::lean_dec_ref(v_a_3207_);
    return v_res_3212_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(
    mut v_00_u03b1_3213_: *mut crate::leanh::LeanObject,
    mut v_msg_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
    mut v___y_3216_: *mut crate::leanh::LeanObject,
    mut v___y_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3220_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
    return v___x_3220_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_3221_: *mut crate::leanh::LeanObject,
    mut v_msg_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3228_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0(v_00_u03b1_3221_, v_msg_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
    crate::leanh::lean_dec(v___y_3226_);
    crate::leanh::lean_dec_ref(v___y_3225_);
    crate::leanh::lean_dec(v___y_3224_);
    crate::leanh::lean_dec_ref(v___y_3223_);
    return v_res_3228_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(
    mut v___x_3229_: u8,
    mut v_as_3230_: *mut crate::leanh::LeanObject,
    mut v_i_3231_: usize,
    mut v_stop_3232_: usize,
) -> u8 {
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: u8 = 0;
    let mut v___y_3236_: u8 = 0;
    let mut v___x_3237_: usize = 0;
    let mut v___x_3238_: usize = 0;
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: u8 = 0;
    let mut v___x_3242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3233_ = lean_usize_dec_eq(v_i_3231_, v_stop_3232_);
                if v___x_3233_ == 0 {
                    v___x_3234_ = 1;
                    v___x_3240_ = lean_array_uget_borrowed(v_as_3230_, v_i_3231_);
                    v___x_3241_ = l_Lean_Expr_isFVar(v___x_3240_);
                    if v___x_3241_ == 0 {
                        v___y_3236_ = v___x_3229_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3236_ = v___x_3233_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3242_ = 0;
                    return v___x_3242_;
                }
            }
            1 => {
                if v___y_3236_ == 0 {
                    v___x_3237_ = 1usize;
                    v___x_3238_ = lean_usize_add(v_i_3231_, v___x_3237_);
                    v_i_3231_ = v___x_3238_;
                    state = 0;
                    continue;
                } else {
                    return v___x_3234_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0___boxed(
    mut v___x_3243_: *mut crate::leanh::LeanObject,
    mut v_as_3244_: *mut crate::leanh::LeanObject,
    mut v_i_3245_: *mut crate::leanh::LeanObject,
    mut v_stop_3246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_579__boxed_3247_: u8 = 0;
    let mut v_i_boxed_3248_: usize = 0;
    let mut v_stop_boxed_3249_: usize = 0;
    let mut v_res_3250_: u8 = 0;
    let mut v_r_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_579__boxed_3247_ = (crate::leanh::lean_unbox(v___x_3243_) as u8);
    v_i_boxed_3248_ = crate::leanh::lean_unbox_usize(v_i_3245_);
    crate::leanh::lean_dec(v_i_3245_);
    v_stop_boxed_3249_ = crate::leanh::lean_unbox_usize(v_stop_3246_);
    crate::leanh::lean_dec(v_stop_3246_);
    v_res_3250_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(v___x_579__boxed_3247_, v_as_3244_, v_i_boxed_3248_, v_stop_boxed_3249_);
    crate::leanh::lean_dec_ref(v_as_3244_);
    v_r_3251_ = crate::leanh::lean_box((v_res_3250_) as usize);
    return v_r_3251_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3253_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__0;
    v___x_3254_ = l_Lean_stringToMessageData(v___x_3253_);
    return v___x_3254_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
    v___x_3257_ = l_Lean_stringToMessageData(v___x_3256_);
    return v___x_3257_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(
    mut v_declName_3258_: *mut crate::leanh::LeanObject,
    mut v_motive_3259_: *mut crate::leanh::LeanObject,
    mut v_motiveArgs_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
    mut v_a_3262_: *mut crate::leanh::LeanObject,
    mut v_a_3263_: *mut crate::leanh::LeanObject,
    mut v_a_3264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3267_: u8 = 0;
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3275_: u8 = 0;
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: u8 = 0;
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: u8 = 0;
    let mut v___x_3282_: usize = 0;
    let mut v___x_3283_: usize = 0;
    let mut v___x_3284_: u8 = 0;
    let mut v___x_3285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3278_ = l_Lean_Expr_isFVar(v_motive_3259_);
                if v___x_3278_ == 0 {
                    v___y_3275_ = v___x_3278_;
                    state = 2;
                    continue;
                } else {
                    v___x_3279_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3280_ = lean_array_get_size(v_motiveArgs_3260_);
                    v___x_3281_ = lean_nat_dec_lt(v___x_3279_, v___x_3280_);
                    if v___x_3281_ == 0 {
                        v___y_3275_ = v___x_3278_;
                        state = 2;
                        continue;
                    } else {
                        if v___x_3281_ == 0 {
                            v___y_3275_ = v___x_3278_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3282_ = 0usize;
                            v___x_3283_ = lean_usize_of_nat(v___x_3280_);
                            v___x_3284_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive_spec__0(v___x_3278_, v_motiveArgs_3260_, v___x_3282_, v___x_3283_);
                            if v___x_3284_ == 0 {
                                v___y_3275_ = v___x_3278_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3285_ = 0;
                                v___y_3267_ = v___x_3285_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3268_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
                v___x_3269_ = l_Lean_MessageData_ofConstName(v_declName_3258_, v___y_3267_);
                v___x_3270_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3270_, 0, v___x_3268_);
                crate::leanh::lean_ctor_set(v___x_3270_, 1, v___x_3269_);
                v___x_3271_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3);
                v___x_3272_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3272_, 0, v___x_3270_);
                crate::leanh::lean_ctor_set(v___x_3272_, 1, v___x_3271_);
                v___x_3273_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_3272_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
                return v___x_3273_;
            }
            2 => {
                if v___y_3275_ == 0 {
                    v___y_3267_ = v___y_3275_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_3258_);
                    v___x_3276_ = crate::leanh::lean_box(0);
                    v___x_3277_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3277_, 0, v___x_3276_);
                    return v___x_3277_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___boxed(
    mut v_declName_3286_: *mut crate::leanh::LeanObject,
    mut v_motive_3287_: *mut crate::leanh::LeanObject,
    mut v_motiveArgs_3288_: *mut crate::leanh::LeanObject,
    mut v_a_3289_: *mut crate::leanh::LeanObject,
    mut v_a_3290_: *mut crate::leanh::LeanObject,
    mut v_a_3291_: *mut crate::leanh::LeanObject,
    mut v_a_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3294_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(
        v_declName_3286_,
        v_motive_3287_,
        v_motiveArgs_3288_,
        v_a_3289_,
        v_a_3290_,
        v_a_3291_,
        v_a_3292_,
    );
    crate::leanh::lean_dec(v_a_3292_);
    crate::leanh::lean_dec_ref(v_a_3291_);
    crate::leanh::lean_dec(v_a_3290_);
    crate::leanh::lean_dec_ref(v_a_3289_);
    crate::leanh::lean_dec_ref(v_motiveArgs_3288_);
    crate::leanh::lean_dec_ref(v_motive_3287_);
    return v_res_3294_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(
    mut v_xs_3295_: *mut crate::leanh::LeanObject,
    mut v_motive_3296_: *mut crate::leanh::LeanObject,
    mut v_i_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: u8 = 0;
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: u8 = 0;
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3298_ = lean_array_get_size(v_xs_3295_);
                v___x_3299_ = lean_nat_dec_lt(v_i_3297_, v___x_3298_);
                if v___x_3299_ == 0 {
                    return v_i_3297_;
                } else {
                    v___x_3300_ = lean_array_fget_borrowed(v_xs_3295_, v_i_3297_);
                    v___x_3301_ = lean_expr_eqv(v_motive_3296_, v___x_3300_);
                    if v___x_3301_ == 0 {
                        v___x_3302_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3303_ = lean_nat_add(v_i_3297_, v___x_3302_);
                        crate::leanh::lean_dec(v_i_3297_);
                        v_i_3297_ = v___x_3303_;
                        state = 0;
                        continue;
                    } else {
                        return v_i_3297_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams___boxed(
    mut v_xs_3305_: *mut crate::leanh::LeanObject,
    mut v_motive_3306_: *mut crate::leanh::LeanObject,
    mut v_i_3307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3308_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(
        v_xs_3305_,
        v_motive_3306_,
        v_i_3307_,
    );
    crate::leanh::lean_dec_ref(v_motive_3306_);
    crate::leanh::lean_dec_ref(v_xs_3305_);
    return v_res_3308_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(
    mut v_xs_3309_: *mut crate::leanh::LeanObject,
    mut v_v_3310_: *mut crate::leanh::LeanObject,
    mut v_i_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: u8 = 0;
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3312_ = lean_array_get_size(v_xs_3309_);
                v___x_3313_ = lean_nat_dec_lt(v_i_3311_, v___x_3312_);
                if v___x_3313_ == 0 {
                    crate::leanh::lean_dec(v_i_3311_);
                    v___x_3314_ = crate::leanh::lean_box(0);
                    return v___x_3314_;
                } else {
                    v___x_3315_ = lean_array_fget_borrowed(v_xs_3309_, v_i_3311_);
                    v___x_3316_ = lean_expr_eqv(v___x_3315_, v_v_3310_);
                    if v___x_3316_ == 0 {
                        v___x_3317_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3318_ = lean_nat_add(v_i_3311_, v___x_3317_);
                        crate::leanh::lean_dec(v_i_3311_);
                        v_i_3311_ = v___x_3318_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3320_, 0, v_i_3311_);
                        return v___x_3320_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1___boxed(
    mut v_xs_3321_: *mut crate::leanh::LeanObject,
    mut v_v_3322_: *mut crate::leanh::LeanObject,
    mut v_i_3323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3324_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(v_xs_3321_, v_v_3322_, v_i_3323_);
    crate::leanh::lean_dec_ref(v_v_3322_);
    crate::leanh::lean_dec_ref(v_xs_3321_);
    return v_res_3324_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(
    mut v_xs_3325_: *mut crate::leanh::LeanObject,
    mut v_v_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3328_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0_spec__1(v_xs_3325_, v_v_3326_, v___x_3327_);
    return v___x_3328_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0___boxed(
    mut v_xs_3329_: *mut crate::leanh::LeanObject,
    mut v_v_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(v_xs_3329_, v_v_3330_);
    crate::leanh::lean_dec_ref(v_v_3330_);
    crate::leanh::lean_dec_ref(v_xs_3329_);
    return v_res_3331_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(
    mut v_xs_3332_: *mut crate::leanh::LeanObject,
    mut v_v_3333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3339_: u8 = 0;
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3334_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0_spec__0(v_xs_3332_, v_v_3333_);
                if crate::leanh::lean_obj_tag(v___x_3334_) == 0 {
                    v___x_3335_ = crate::leanh::lean_box(0);
                    return v___x_3335_;
                } else {
                    v_val_3336_ = crate::leanh::lean_ctor_get(v___x_3334_, 0);
                    v_isSharedCheck_3343_ = (!crate::leanh::lean_is_exclusive(v___x_3334_)) as u8;
                    if v_isSharedCheck_3343_ == 0 {
                        v___x_3338_ = v___x_3334_;
                        v_isShared_3339_ = v_isSharedCheck_3343_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3336_);
                        crate::leanh::lean_dec(v___x_3334_);
                        v___x_3338_ = crate::leanh::lean_box(0);
                        v_isShared_3339_ = v_isSharedCheck_3343_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3339_ == 0 {
                    v___x_3341_ = v___x_3338_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_val_3336_);
                    v___x_3341_ = v_reuseFailAlloc_3342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0___boxed(
    mut v_xs_3344_: *mut crate::leanh::LeanObject,
    mut v_v_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3346_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(v_xs_3344_, v_v_3345_);
    crate::leanh::lean_dec_ref(v_v_3345_);
    crate::leanh::lean_dec_ref(v_xs_3344_);
    return v_res_3346_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_as_3348_: *mut crate::leanh::LeanObject,
    mut v_i_3349_: usize,
    mut v_stop_3350_: usize,
) -> u8 {
    let mut v___x_3351_: u8 = 0;
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: u8 = 0;
    let mut v___x_3354_: usize = 0;
    let mut v___x_3355_: usize = 0;
    let mut v___x_3357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3351_ = lean_usize_dec_eq(v_i_3349_, v_stop_3350_);
                if v___x_3351_ == 0 {
                    v___x_3352_ = lean_array_uget_borrowed(v_as_3348_, v_i_3349_);
                    v___x_3353_ = lean_expr_eqv(v_a_3347_, v___x_3352_);
                    if v___x_3353_ == 0 {
                        v___x_3354_ = 1usize;
                        v___x_3355_ = lean_usize_add(v_i_3349_, v___x_3354_);
                        v_i_3349_ = v___x_3355_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3353_;
                    }
                } else {
                    v___x_3357_ = 0;
                    return v___x_3357_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2___boxed(
    mut v_a_3358_: *mut crate::leanh::LeanObject,
    mut v_as_3359_: *mut crate::leanh::LeanObject,
    mut v_i_3360_: *mut crate::leanh::LeanObject,
    mut v_stop_3361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3362_: usize = 0;
    let mut v_stop_boxed_3363_: usize = 0;
    let mut v_res_3364_: u8 = 0;
    let mut v_r_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3362_ = crate::leanh::lean_unbox_usize(v_i_3360_);
    crate::leanh::lean_dec(v_i_3360_);
    v_stop_boxed_3363_ = crate::leanh::lean_unbox_usize(v_stop_3361_);
    crate::leanh::lean_dec(v_stop_3361_);
    v_res_3364_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(v_a_3358_, v_as_3359_, v_i_boxed_3362_, v_stop_boxed_3363_);
    crate::leanh::lean_dec_ref(v_as_3359_);
    crate::leanh::lean_dec_ref(v_a_3358_);
    v_r_3365_ = crate::leanh::lean_box((v_res_3364_) as usize);
    return v_r_3365_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(
    mut v_as_3366_: *mut crate::leanh::LeanObject,
    mut v_a_3367_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: u8 = 0;
    v___x_3368_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3369_ = lean_array_get_size(v_as_3366_);
    v___x_3370_ = lean_nat_dec_lt(v___x_3368_, v___x_3369_);
    if v___x_3370_ == 0 {
        return v___x_3370_;
    } else {
        if v___x_3370_ == 0 {
            return v___x_3370_;
        } else {
            let mut v___x_3371_: usize = 0;
            let mut v___x_3372_: usize = 0;
            let mut v___x_3373_: u8 = 0;
            v___x_3371_ = 0usize;
            v___x_3372_ = lean_usize_of_nat(v___x_3369_);
            v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1_spec__2(v_a_3367_, v_as_3366_, v___x_3371_, v___x_3372_);
            return v___x_3373_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1___boxed(
    mut v_as_3374_: *mut crate::leanh::LeanObject,
    mut v_a_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3376_: u8 = 0;
    let mut v_r_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3376_ = l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(v_as_3374_, v_a_3375_);
    crate::leanh::lean_dec_ref(v_a_3375_);
    crate::leanh::lean_dec_ref(v_as_3374_);
    v_r_3377_ = crate::leanh::lean_box((v_res_3376_) as usize);
    return v_r_3377_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3379_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__0;
    v___x_3380_ = l_Lean_stringToMessageData(v___x_3379_);
    return v___x_3380_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3382_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2;
    v___x_3383_ = l_Lean_stringToMessageData(v___x_3382_);
    return v___x_3383_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3385_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4;
    v___x_3386_ = l_Lean_stringToMessageData(v___x_3385_);
    return v___x_3386_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3388_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6;
    v___x_3389_ = l_Lean_stringToMessageData(v___x_3388_);
    return v___x_3389_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8;
    v___x_3392_ = l_Lean_stringToMessageData(v___x_3391_);
    return v___x_3392_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(
    mut v_declName_3393_: *mut crate::leanh::LeanObject,
    mut v_majorPos_x3f_3394_: *mut crate::leanh::LeanObject,
    mut v_xs_3395_: *mut crate::leanh::LeanObject,
    mut v_motiveArgs_3396_: *mut crate::leanh::LeanObject,
    mut v_a_3397_: *mut crate::leanh::LeanObject,
    mut v_a_3398_: *mut crate::leanh::LeanObject,
    mut v_a_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_major_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: u8 = 0;
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3423_: u8 = 0;
    let mut v___x_3424_: u8 = 0;
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3431_: u8 = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: u8 = 0;
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3445_: u8 = 0;
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3449_: u8 = 0;
    let mut v_val_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: u8 = 0;
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_major_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depElim_3467_: u8 = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_majorPos_x3f_3394_) == 0 {
                    v___x_3402_ = l_Lean_instInhabitedExpr;
                    v___x_3432_ = lean_array_get_size(v_motiveArgs_3396_);
                    v___x_3433_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3434_ = lean_nat_dec_eq(v___x_3432_, v___x_3433_);
                    if v___x_3434_ == 0 {
                        v___y_3404_ = v_a_3397_;
                        v___y_3405_ = v_a_3398_;
                        v___y_3406_ = v_a_3399_;
                        v___y_3407_ = v_a_3400_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3435_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3);
                        v___x_3436_ = 0;
                        v___x_3437_ = l_Lean_MessageData_ofConstName(v_declName_3393_, v___x_3436_);
                        v___x_3438_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3438_, 0, v___x_3435_);
                        crate::leanh::lean_ctor_set(v___x_3438_, 1, v___x_3437_);
                        v___x_3439_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5);
                        v___x_3440_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3440_, 0, v___x_3438_);
                        crate::leanh::lean_ctor_set(v___x_3440_, 1, v___x_3439_);
                        v___x_3441_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_3440_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
                        v_a_3442_ = crate::leanh::lean_ctor_get(v___x_3441_, 0);
                        v_isSharedCheck_3449_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3441_)) as u8;
                        if v_isSharedCheck_3449_ == 0 {
                            v___x_3444_ = v___x_3441_;
                            v_isShared_3445_ = v_isSharedCheck_3449_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3442_);
                            crate::leanh::lean_dec(v___x_3441_);
                            v___x_3444_ = crate::leanh::lean_box(0);
                            v_isShared_3445_ = v_isSharedCheck_3449_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_3393_);
                    v_val_3450_ = crate::leanh::lean_ctor_get(v_majorPos_x3f_3394_, 0);
                    v_isSharedCheck_3474_ =
                        (!crate::leanh::lean_is_exclusive(v_majorPos_x3f_3394_)) as u8;
                    if v_isSharedCheck_3474_ == 0 {
                        v___x_3452_ = v_majorPos_x3f_3394_;
                        v_isShared_3453_ = v_isSharedCheck_3474_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3450_);
                        crate::leanh::lean_dec(v_majorPos_x3f_3394_);
                        v___x_3452_ = crate::leanh::lean_box(0);
                        v_isShared_3453_ = v_isSharedCheck_3474_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3408_ = lean_array_get_size(v_motiveArgs_3396_);
                v___x_3409_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3410_ = lean_nat_sub(v___x_3408_, v___x_3409_);
                v_major_3411_ =
                    lean_array_get_borrowed(v___x_3402_, v_motiveArgs_3396_, v___x_3410_);
                crate::leanh::lean_dec(v___x_3410_);
                v___x_3412_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__0(v_xs_3395_, v_major_3411_);
                if crate::leanh::lean_obj_tag(v___x_3412_) == 0 {
                    v___x_3413_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1);
                    v___x_3414_ = 0;
                    v___x_3415_ = l_Lean_MessageData_ofConstName(v_declName_3393_, v___x_3414_);
                    v___x_3416_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3416_, 0, v___x_3413_);
                    crate::leanh::lean_ctor_set(v___x_3416_, 1, v___x_3415_);
                    v___x_3417_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
                    v___x_3418_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3418_, 0, v___x_3416_);
                    crate::leanh::lean_ctor_set(v___x_3418_, 1, v___x_3417_);
                    v___x_3419_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_3418_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
                    return v___x_3419_;
                } else {
                    crate::leanh::lean_dec(v_declName_3393_);
                    v_val_3420_ = crate::leanh::lean_ctor_get(v___x_3412_, 0);
                    v_isSharedCheck_3431_ = (!crate::leanh::lean_is_exclusive(v___x_3412_)) as u8;
                    if v_isSharedCheck_3431_ == 0 {
                        v___x_3422_ = v___x_3412_;
                        v_isShared_3423_ = v_isSharedCheck_3431_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3420_);
                        crate::leanh::lean_dec(v___x_3412_);
                        v___x_3422_ = crate::leanh::lean_box(0);
                        v_isShared_3423_ = v_isSharedCheck_3431_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3424_ = 1;
                v___x_3425_ = crate::leanh::lean_box((v___x_3424_) as usize);
                v___x_3426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3426_, 0, v_val_3420_);
                crate::leanh::lean_ctor_set(v___x_3426_, 1, v___x_3425_);
                crate::leanh::lean_inc(v_major_3411_);
                v___x_3427_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3427_, 0, v_major_3411_);
                crate::leanh::lean_ctor_set(v___x_3427_, 1, v___x_3426_);
                if v_isShared_3423_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3422_, 0);
                    crate::leanh::lean_ctor_set(v___x_3422_, 0, v___x_3427_);
                    v___x_3429_ = v___x_3422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3430_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
                    v___x_3429_ = v_reuseFailAlloc_3430_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3429_;
            }
            4 => {
                if v_isShared_3445_ == 0 {
                    v___x_3447_ = v___x_3444_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
                    v___x_3447_ = v_reuseFailAlloc_3448_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3447_;
            }
            6 => {
                v___x_3454_ = lean_array_get_size(v_xs_3395_);
                v___x_3455_ = lean_nat_dec_lt(v_val_3450_, v___x_3454_);
                if v___x_3455_ == 0 {
                    crate::leanh::lean_dec(v_val_3450_);
                    v___x_3456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7);
                    v___x_3457_ = l_Nat_reprFast(v___x_3454_);
                    if v_isShared_3453_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3452_, 3);
                        crate::leanh::lean_ctor_set(v___x_3452_, 0, v___x_3457_);
                        v___x_3459_ = v___x_3452_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3465_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3457_);
                        v___x_3459_ = v_reuseFailAlloc_3465_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_major_3466_ = lean_array_fget_borrowed(v_xs_3395_, v_val_3450_);
                    v_depElim_3467_ = l_Array_contains___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim_spec__1(v_motiveArgs_3396_, v_major_3466_);
                    v___x_3468_ = crate::leanh::lean_box((v_depElim_3467_) as usize);
                    v___x_3469_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3469_, 0, v_val_3450_);
                    crate::leanh::lean_ctor_set(v___x_3469_, 1, v___x_3468_);
                    crate::leanh::lean_inc(v_major_3466_);
                    v___x_3470_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3470_, 0, v_major_3466_);
                    crate::leanh::lean_ctor_set(v___x_3470_, 1, v___x_3469_);
                    if v_isShared_3453_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3452_, 0);
                        crate::leanh::lean_ctor_set(v___x_3452_, 0, v___x_3470_);
                        v___x_3472_ = v___x_3452_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
                        v___x_3472_ = v_reuseFailAlloc_3473_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3460_ = l_Lean_MessageData_ofFormat(v___x_3459_);
                v___x_3461_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3461_, 0, v___x_3456_);
                crate::leanh::lean_ctor_set(v___x_3461_, 1, v___x_3460_);
                v___x_3462_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__9);
                v___x_3463_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3463_, 0, v___x_3461_);
                crate::leanh::lean_ctor_set(v___x_3463_, 1, v___x_3462_);
                v___x_3464_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_3463_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
                return v___x_3464_;
            }
            8 => {
                return v___x_3472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___boxed(
    mut v_declName_3475_: *mut crate::leanh::LeanObject,
    mut v_majorPos_x3f_3476_: *mut crate::leanh::LeanObject,
    mut v_xs_3477_: *mut crate::leanh::LeanObject,
    mut v_motiveArgs_3478_: *mut crate::leanh::LeanObject,
    mut v_a_3479_: *mut crate::leanh::LeanObject,
    mut v_a_3480_: *mut crate::leanh::LeanObject,
    mut v_a_3481_: *mut crate::leanh::LeanObject,
    mut v_a_3482_: *mut crate::leanh::LeanObject,
    mut v_a_3483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3484_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(
        v_declName_3475_,
        v_majorPos_x3f_3476_,
        v_xs_3477_,
        v_motiveArgs_3478_,
        v_a_3479_,
        v_a_3480_,
        v_a_3481_,
        v_a_3482_,
    );
    crate::leanh::lean_dec(v_a_3482_);
    crate::leanh::lean_dec_ref(v_a_3481_);
    crate::leanh::lean_dec(v_a_3480_);
    crate::leanh::lean_dec_ref(v_a_3479_);
    crate::leanh::lean_dec_ref(v_motiveArgs_3478_);
    crate::leanh::lean_dec_ref(v_xs_3477_);
    return v_res_3484_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(
    mut v___x_3485_: *mut crate::leanh::LeanObject,
    mut v_as_3486_: *mut crate::leanh::LeanObject,
    mut v_sz_3487_: usize,
    mut v_i_3488_: usize,
    mut v_b_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3502_: u8 = 0;
    let mut v___x_3503_: u8 = 0;
    let mut v_snd_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3507_: u8 = 0;
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: usize = 0;
    let mut v___x_3514_: usize = 0;
    let mut v_reuseFailAlloc_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_unused_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut v_unused_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut v_a_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3537_: u8 = 0;
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3495_ = lean_usize_dec_lt(v_i_3488_, v_sz_3487_);
                if v___x_3495_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3485_);
                    v___x_3496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3496_, 0, v_b_3489_);
                    return v___x_3496_;
                } else {
                    v_a_3497_ = lean_array_uget_borrowed(v_as_3486_, v_i_3488_);
                    crate::leanh::lean_inc_ref(v___x_3485_);
                    crate::leanh::lean_inc(v_a_3497_);
                    v___x_3498_ = l_Lean_Meta_isExprDefEq(
                        v_a_3497_,
                        v___x_3485_,
                        v___y_3490_,
                        v___y_3491_,
                        v___y_3492_,
                        v___y_3493_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3498_) == 0 {
                        v_a_3499_ = crate::leanh::lean_ctor_get(v___x_3498_, 0);
                        v_isSharedCheck_3533_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3498_)) as u8;
                        if v_isSharedCheck_3533_ == 0 {
                            v___x_3501_ = v___x_3498_;
                            v_isShared_3502_ = v_isSharedCheck_3533_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3499_);
                            crate::leanh::lean_dec(v___x_3498_);
                            v___x_3501_ = crate::leanh::lean_box(0);
                            v_isShared_3502_ = v_isSharedCheck_3533_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3489_);
                        crate::leanh::lean_dec_ref(v___x_3485_);
                        v_a_3534_ = crate::leanh::lean_ctor_get(v___x_3498_, 0);
                        v_isSharedCheck_3541_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3498_)) as u8;
                        if v_isSharedCheck_3541_ == 0 {
                            v___x_3536_ = v___x_3498_;
                            v_isShared_3537_ = v_isSharedCheck_3541_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3534_);
                            crate::leanh::lean_dec(v___x_3498_);
                            v___x_3536_ = crate::leanh::lean_box(0);
                            v_isShared_3537_ = v_isSharedCheck_3541_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3503_ = (crate::leanh::lean_unbox(v_a_3499_) as u8);
                crate::leanh::lean_dec(v_a_3499_);
                if v___x_3503_ == 0 {
                    crate::leanh::lean_del_object(v___x_3501_);
                    v_snd_3504_ = crate::leanh::lean_ctor_get(v_b_3489_, 1);
                    v_isSharedCheck_3517_ = (!crate::leanh::lean_is_exclusive(v_b_3489_)) as u8;
                    if v_isSharedCheck_3517_ == 0 {
                        v_unused_3518_ = crate::leanh::lean_ctor_get(v_b_3489_, 0);
                        crate::leanh::lean_dec(v_unused_3518_);
                        v___x_3506_ = v_b_3489_;
                        v_isShared_3507_ = v_isSharedCheck_3517_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3504_);
                        crate::leanh::lean_dec(v_b_3489_);
                        v___x_3506_ = crate::leanh::lean_box(0);
                        v_isShared_3507_ = v_isSharedCheck_3517_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3485_);
                    v_snd_3519_ = crate::leanh::lean_ctor_get(v_b_3489_, 1);
                    v_isSharedCheck_3531_ = (!crate::leanh::lean_is_exclusive(v_b_3489_)) as u8;
                    if v_isSharedCheck_3531_ == 0 {
                        v_unused_3532_ = crate::leanh::lean_ctor_get(v_b_3489_, 0);
                        crate::leanh::lean_dec(v_unused_3532_);
                        v___x_3521_ = v_b_3489_;
                        v_isShared_3522_ = v_isSharedCheck_3531_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3519_);
                        crate::leanh::lean_dec(v_b_3489_);
                        v___x_3521_ = crate::leanh::lean_box(0);
                        v_isShared_3522_ = v_isSharedCheck_3531_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3508_ = crate::leanh::lean_box(0);
                v___x_3509_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3510_ = lean_nat_add(v_snd_3504_, v___x_3509_);
                crate::leanh::lean_dec(v_snd_3504_);
                if v_isShared_3507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3506_, 1, v___x_3510_);
                    crate::leanh::lean_ctor_set(v___x_3506_, 0, v___x_3508_);
                    v___x_3512_ = v___x_3506_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 1, v___x_3510_);
                    v___x_3512_ = v_reuseFailAlloc_3516_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3513_ = 1usize;
                v___x_3514_ = lean_usize_add(v_i_3488_, v___x_3513_);
                v_i_3488_ = v___x_3514_;
                v_b_3489_ = v___x_3512_;
                state = 0;
                continue;
            }
            4 => {
                crate::leanh::lean_inc(v_snd_3519_);
                v___x_3523_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3523_, 0, v_snd_3519_);
                v___x_3524_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3524_, 0, v___x_3523_);
                if v_isShared_3522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3521_, 0, v___x_3524_);
                    v___x_3526_ = v___x_3521_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3530_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_snd_3519_);
                    v___x_3526_ = v_reuseFailAlloc_3530_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3502_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3501_, 0, v___x_3526_);
                    v___x_3528_ = v___x_3501_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
                    v___x_3528_ = v_reuseFailAlloc_3529_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3528_;
            }
            7 => {
                if v_isShared_3537_ == 0 {
                    v___x_3539_ = v___x_3536_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
                    v___x_3539_ = v_reuseFailAlloc_3540_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0___boxed(
    mut v___x_3542_: *mut crate::leanh::LeanObject,
    mut v_as_3543_: *mut crate::leanh::LeanObject,
    mut v_sz_3544_: *mut crate::leanh::LeanObject,
    mut v_i_3545_: *mut crate::leanh::LeanObject,
    mut v_b_3546_: *mut crate::leanh::LeanObject,
    mut v___y_3547_: *mut crate::leanh::LeanObject,
    mut v___y_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
    mut v___y_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3552_: usize = 0;
    let mut v_i_boxed_3553_: usize = 0;
    let mut v_res_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3552_ = crate::leanh::lean_unbox_usize(v_sz_3544_);
    crate::leanh::lean_dec(v_sz_3544_);
    v_i_boxed_3553_ = crate::leanh::lean_unbox_usize(v_i_3545_);
    crate::leanh::lean_dec(v_i_3545_);
    v_res_3554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_3542_, v_as_3543_, v_sz_boxed_3552_, v_i_boxed_3553_, v_b_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
    crate::leanh::lean_dec(v___y_3550_);
    crate::leanh::lean_dec_ref(v___y_3549_);
    crate::leanh::lean_dec(v___y_3548_);
    crate::leanh::lean_dec_ref(v___y_3547_);
    crate::leanh::lean_dec_ref(v_as_3543_);
    return v_res_3554_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3556_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__0;
    v___x_3557_ = l_Lean_stringToMessageData(v___x_3556_);
    return v___x_3557_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(
    mut v_upperBound_3561_: *mut crate::leanh::LeanObject,
    mut v_xs_3562_: *mut crate::leanh::LeanObject,
    mut v_declName_3563_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
    mut v_b_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
    mut v___y_3568_: *mut crate::leanh::LeanObject,
    mut v___y_3569_: *mut crate::leanh::LeanObject,
    mut v___y_3570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: u8 = 0;
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3606_: u8 = 0;
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3610_: u8 = 0;
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3613_: usize = 0;
    let mut v___x_3614_: usize = 0;
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3623_: u8 = 0;
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3577_ = lean_nat_dec_lt(v_a_3565_, v_upperBound_3561_);
                if v___x_3577_ == 0 {
                    crate::leanh::lean_dec(v_a_3565_);
                    crate::leanh::lean_dec(v_declName_3563_);
                    v___x_3578_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3578_, 0, v_b_3566_);
                    return v___x_3578_;
                } else {
                    v___x_3579_ = l_Lean_instInhabitedExpr;
                    v___x_3580_ = lean_array_get_borrowed(v___x_3579_, v_xs_3562_, v_a_3565_);
                    v___x_3611_ = crate::leanh::lean_box(0);
                    v___x_3612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2;
                    v_sz_3613_ = lean_array_size(v_Iargs_3564_);
                    v___x_3614_ = 0usize;
                    crate::leanh::lean_inc(v___x_3580_);
                    v___x_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_3580_, v_Iargs_3564_, v_sz_3613_, v___x_3614_, v___x_3612_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
                    if crate::leanh::lean_obj_tag(v___x_3615_) == 0 {
                        v_a_3616_ = crate::leanh::lean_ctor_get(v___x_3615_, 0);
                        crate::leanh::lean_inc(v_a_3616_);
                        crate::leanh::lean_dec_ref_known(v___x_3615_, 1);
                        v_fst_3617_ = crate::leanh::lean_ctor_get(v_a_3616_, 0);
                        crate::leanh::lean_inc(v_fst_3617_);
                        crate::leanh::lean_dec(v_a_3616_);
                        if crate::leanh::lean_obj_tag(v_fst_3617_) == 0 {
                            v_a_3582_ = v___x_3611_;
                            state = 2;
                            continue;
                        } else {
                            v_val_3618_ = crate::leanh::lean_ctor_get(v_fst_3617_, 0);
                            crate::leanh::lean_inc(v_val_3618_);
                            crate::leanh::lean_dec_ref_known(v_fst_3617_, 1);
                            if crate::leanh::lean_obj_tag(v_val_3618_) == 0 {
                                v_a_3582_ = v_val_3618_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3619_ = lean_array_push(v_b_3566_, v_val_3618_);
                                v_a_3573_ = v___x_3619_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3566_);
                        crate::leanh::lean_dec(v_a_3565_);
                        crate::leanh::lean_dec(v_declName_3563_);
                        v_a_3620_ = crate::leanh::lean_ctor_get(v___x_3615_, 0);
                        v_isSharedCheck_3627_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3615_)) as u8;
                        if v_isSharedCheck_3627_ == 0 {
                            v___x_3622_ = v___x_3615_;
                            v_isShared_3623_ = v_isSharedCheck_3627_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3620_);
                            crate::leanh::lean_dec(v___x_3615_);
                            v___x_3622_ = crate::leanh::lean_box(0);
                            v_isShared_3623_ = v_isSharedCheck_3627_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3574_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3575_ = lean_nat_add(v_a_3565_, v___x_3574_);
                crate::leanh::lean_dec(v_a_3565_);
                v_a_3565_ = v___x_3575_;
                v_b_3566_ = v_a_3573_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3583_ = l_Lean_Expr_fvarId_x21(v___x_3580_);
                v___x_3584_ = l_Lean_FVarId_getDecl___redArg(
                    v___x_3583_,
                    v___y_3567_,
                    v___y_3569_,
                    v___y_3570_,
                );
                if crate::leanh::lean_obj_tag(v___x_3584_) == 0 {
                    v_a_3585_ = crate::leanh::lean_ctor_get(v___x_3584_, 0);
                    crate::leanh::lean_inc(v_a_3585_);
                    crate::leanh::lean_dec_ref_known(v___x_3584_, 1);
                    v___x_3586_ = l_Lean_LocalDecl_binderInfo(v_a_3585_);
                    crate::leanh::lean_dec(v_a_3585_);
                    v___x_3587_ = l_Lean_BinderInfo_isInstImplicit(v___x_3586_);
                    if v___x_3587_ == 0 {
                        crate::leanh::lean_dec(v_a_3582_);
                        v___x_3588_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
                        crate::leanh::lean_inc(v_declName_3563_);
                        v___x_3589_ = l_Lean_MessageData_ofConstName(v_declName_3563_, v___x_3587_);
                        v___x_3590_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3590_, 0, v___x_3588_);
                        crate::leanh::lean_ctor_set(v___x_3590_, 1, v___x_3589_);
                        v___x_3591_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__1);
                        v___x_3592_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3592_, 0, v___x_3590_);
                        crate::leanh::lean_ctor_set(v___x_3592_, 1, v___x_3591_);
                        v___x_3593_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_3592_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
                        if crate::leanh::lean_obj_tag(v___x_3593_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3593_, 1);
                            v_a_3573_ = v_b_3566_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_3566_);
                            crate::leanh::lean_dec(v_a_3565_);
                            crate::leanh::lean_dec(v_declName_3563_);
                            v_a_3594_ = crate::leanh::lean_ctor_get(v___x_3593_, 0);
                            v_isSharedCheck_3601_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3593_)) as u8;
                            if v_isSharedCheck_3601_ == 0 {
                                v___x_3596_ = v___x_3593_;
                                v_isShared_3597_ = v_isSharedCheck_3601_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3594_);
                                crate::leanh::lean_dec(v___x_3593_);
                                v___x_3596_ = crate::leanh::lean_box(0);
                                v_isShared_3597_ = v_isSharedCheck_3601_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_3602_ = lean_array_push(v_b_3566_, v_a_3582_);
                        v_a_3573_ = v___x_3602_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3582_);
                    crate::leanh::lean_dec_ref(v_b_3566_);
                    crate::leanh::lean_dec(v_a_3565_);
                    crate::leanh::lean_dec(v_declName_3563_);
                    v_a_3603_ = crate::leanh::lean_ctor_get(v___x_3584_, 0);
                    v_isSharedCheck_3610_ = (!crate::leanh::lean_is_exclusive(v___x_3584_)) as u8;
                    if v_isSharedCheck_3610_ == 0 {
                        v___x_3605_ = v___x_3584_;
                        v_isShared_3606_ = v_isSharedCheck_3610_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3603_);
                        crate::leanh::lean_dec(v___x_3584_);
                        v___x_3605_ = crate::leanh::lean_box(0);
                        v_isShared_3606_ = v_isSharedCheck_3610_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3597_ == 0 {
                    v___x_3599_ = v___x_3596_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
                    v___x_3599_ = v_reuseFailAlloc_3600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3599_;
            }
            5 => {
                if v_isShared_3606_ == 0 {
                    v___x_3608_ = v___x_3605_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
                    v___x_3608_ = v_reuseFailAlloc_3609_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3608_;
            }
            7 => {
                if v_isShared_3623_ == 0 {
                    v___x_3625_ = v___x_3622_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
                    v___x_3625_ = v_reuseFailAlloc_3626_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___boxed(
    mut v_upperBound_3628_: *mut crate::leanh::LeanObject,
    mut v_xs_3629_: *mut crate::leanh::LeanObject,
    mut v_declName_3630_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
    mut v_b_3633_: *mut crate::leanh::LeanObject,
    mut v___y_3634_: *mut crate::leanh::LeanObject,
    mut v___y_3635_: *mut crate::leanh::LeanObject,
    mut v___y_3636_: *mut crate::leanh::LeanObject,
    mut v___y_3637_: *mut crate::leanh::LeanObject,
    mut v___y_3638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3639_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_upperBound_3628_, v_xs_3629_, v_declName_3630_, v_Iargs_3631_, v_a_3632_, v_b_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
    crate::leanh::lean_dec(v___y_3637_);
    crate::leanh::lean_dec_ref(v___y_3636_);
    crate::leanh::lean_dec(v___y_3635_);
    crate::leanh::lean_dec_ref(v___y_3634_);
    crate::leanh::lean_dec_ref(v_Iargs_3631_);
    crate::leanh::lean_dec_ref(v_xs_3629_);
    crate::leanh::lean_dec(v_upperBound_3628_);
    return v_res_3639_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(
    mut v_declName_3642_: *mut crate::leanh::LeanObject,
    mut v_xs_3643_: *mut crate::leanh::LeanObject,
    mut v_numParams_3644_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3645_: *mut crate::leanh::LeanObject,
    mut v_a_3646_: *mut crate::leanh::LeanObject,
    mut v_a_3647_: *mut crate::leanh::LeanObject,
    mut v_a_3648_: *mut crate::leanh::LeanObject,
    mut v_a_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPos_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_a_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3651_ = crate::leanh::lean_unsigned_to_nat(0);
                v_paramsPos_3652_ =
                    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__0;
                v___x_3653_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_numParams_3644_, v_xs_3643_, v_declName_3642_, v_Iargs_3645_, v___x_3651_, v_paramsPos_3652_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
                if crate::leanh::lean_obj_tag(v___x_3653_) == 0 {
                    v_a_3654_ = crate::leanh::lean_ctor_get(v___x_3653_, 0);
                    v_isSharedCheck_3662_ = (!crate::leanh::lean_is_exclusive(v___x_3653_)) as u8;
                    if v_isSharedCheck_3662_ == 0 {
                        v___x_3656_ = v___x_3653_;
                        v_isShared_3657_ = v_isSharedCheck_3662_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3654_);
                        crate::leanh::lean_dec(v___x_3653_);
                        v___x_3656_ = crate::leanh::lean_box(0);
                        v_isShared_3657_ = v_isSharedCheck_3662_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3663_ = crate::leanh::lean_ctor_get(v___x_3653_, 0);
                    v_isSharedCheck_3670_ = (!crate::leanh::lean_is_exclusive(v___x_3653_)) as u8;
                    if v_isSharedCheck_3670_ == 0 {
                        v___x_3665_ = v___x_3653_;
                        v_isShared_3666_ = v_isSharedCheck_3670_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3663_);
                        crate::leanh::lean_dec(v___x_3653_);
                        v___x_3665_ = crate::leanh::lean_box(0);
                        v_isShared_3666_ = v_isSharedCheck_3670_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3658_ = lean_array_to_list(v_a_3654_);
                if v_isShared_3657_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3656_, 0, v___x_3658_);
                    v___x_3660_ = v___x_3656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
                    v___x_3660_ = v_reuseFailAlloc_3661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3660_;
            }
            3 => {
                if v_isShared_3666_ == 0 {
                    v___x_3668_ = v___x_3665_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
                    v___x_3668_ = v_reuseFailAlloc_3669_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3668_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___boxed(
    mut v_declName_3671_: *mut crate::leanh::LeanObject,
    mut v_xs_3672_: *mut crate::leanh::LeanObject,
    mut v_numParams_3673_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3674_: *mut crate::leanh::LeanObject,
    mut v_a_3675_: *mut crate::leanh::LeanObject,
    mut v_a_3676_: *mut crate::leanh::LeanObject,
    mut v_a_3677_: *mut crate::leanh::LeanObject,
    mut v_a_3678_: *mut crate::leanh::LeanObject,
    mut v_a_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3680_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(
        v_declName_3671_,
        v_xs_3672_,
        v_numParams_3673_,
        v_Iargs_3674_,
        v_a_3675_,
        v_a_3676_,
        v_a_3677_,
        v_a_3678_,
    );
    crate::leanh::lean_dec(v_a_3678_);
    crate::leanh::lean_dec_ref(v_a_3677_);
    crate::leanh::lean_dec(v_a_3676_);
    crate::leanh::lean_dec_ref(v_a_3675_);
    crate::leanh::lean_dec_ref(v_Iargs_3674_);
    crate::leanh::lean_dec(v_numParams_3673_);
    crate::leanh::lean_dec_ref(v_xs_3672_);
    return v_res_3680_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(
    mut v_upperBound_3681_: *mut crate::leanh::LeanObject,
    mut v_xs_3682_: *mut crate::leanh::LeanObject,
    mut v_declName_3683_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3684_: *mut crate::leanh::LeanObject,
    mut v_inst_3685_: *mut crate::leanh::LeanObject,
    mut v_R_3686_: *mut crate::leanh::LeanObject,
    mut v_a_3687_: *mut crate::leanh::LeanObject,
    mut v_b_3688_: *mut crate::leanh::LeanObject,
    mut v_c_3689_: *mut crate::leanh::LeanObject,
    mut v___y_3690_: *mut crate::leanh::LeanObject,
    mut v___y_3691_: *mut crate::leanh::LeanObject,
    mut v___y_3692_: *mut crate::leanh::LeanObject,
    mut v___y_3693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3695_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg(v_upperBound_3681_, v_xs_3682_, v_declName_3683_, v_Iargs_3684_, v_a_3687_, v_b_3688_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
    return v___x_3695_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___boxed(
    mut v_upperBound_3696_: *mut crate::leanh::LeanObject,
    mut v_xs_3697_: *mut crate::leanh::LeanObject,
    mut v_declName_3698_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3699_: *mut crate::leanh::LeanObject,
    mut v_inst_3700_: *mut crate::leanh::LeanObject,
    mut v_R_3701_: *mut crate::leanh::LeanObject,
    mut v_a_3702_: *mut crate::leanh::LeanObject,
    mut v_b_3703_: *mut crate::leanh::LeanObject,
    mut v_c_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
    mut v___y_3709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1(v_upperBound_3696_, v_xs_3697_, v_declName_3698_, v_Iargs_3699_, v_inst_3700_, v_R_3701_, v_a_3702_, v_b_3703_, v_c_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
    crate::leanh::lean_dec(v___y_3708_);
    crate::leanh::lean_dec_ref(v___y_3707_);
    crate::leanh::lean_dec(v___y_3706_);
    crate::leanh::lean_dec_ref(v___y_3705_);
    crate::leanh::lean_dec_ref(v_Iargs_3699_);
    crate::leanh::lean_dec_ref(v_xs_3697_);
    crate::leanh::lean_dec(v_upperBound_3696_);
    return v_res_3710_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__0;
    v___x_3713_ = l_Lean_stringToMessageData(v___x_3712_);
    return v___x_3713_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(
    mut v_declName_3714_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3715_: *mut crate::leanh::LeanObject,
    mut v_majorPos_3716_: *mut crate::leanh::LeanObject,
    mut v_numIndices_3717_: *mut crate::leanh::LeanObject,
    mut v_xs_3718_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3719_: *mut crate::leanh::LeanObject,
    mut v_a_3720_: *mut crate::leanh::LeanObject,
    mut v_b_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: u8 = 0;
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut v___x_3748_: u8 = 0;
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3755_: usize = 0;
    let mut v___x_3756_: usize = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3748_ = lean_nat_dec_lt(v_a_3720_, v_upperBound_3715_);
                if v___x_3748_ == 0 {
                    crate::leanh::lean_dec(v_a_3720_);
                    crate::leanh::lean_dec(v_declName_3714_);
                    v___x_3749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3749_, 0, v_b_3721_);
                    return v___x_3749_;
                } else {
                    v___x_3750_ = l_Lean_instInhabitedExpr;
                    v___x_3751_ = lean_nat_sub(v_majorPos_3716_, v_numIndices_3717_);
                    v___x_3752_ = lean_nat_add(v___x_3751_, v_a_3720_);
                    crate::leanh::lean_dec(v___x_3751_);
                    v___x_3753_ = lean_array_get_borrowed(v___x_3750_, v_xs_3718_, v___x_3752_);
                    crate::leanh::lean_dec(v___x_3752_);
                    v___x_3754_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__1___redArg___closed__2;
                    v_sz_3755_ = lean_array_size(v_Iargs_3719_);
                    v___x_3756_ = 0usize;
                    crate::leanh::lean_inc(v___x_3753_);
                    v___x_3757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos_spec__0(v___x_3753_, v_Iargs_3719_, v_sz_3755_, v___x_3756_, v___x_3754_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
                    if crate::leanh::lean_obj_tag(v___x_3757_) == 0 {
                        v_a_3758_ = crate::leanh::lean_ctor_get(v___x_3757_, 0);
                        crate::leanh::lean_inc(v_a_3758_);
                        crate::leanh::lean_dec_ref_known(v___x_3757_, 1);
                        v_fst_3759_ = crate::leanh::lean_ctor_get(v_a_3758_, 0);
                        crate::leanh::lean_inc(v_fst_3759_);
                        crate::leanh::lean_dec(v_a_3758_);
                        if crate::leanh::lean_obj_tag(v_fst_3759_) == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_val_3760_ = crate::leanh::lean_ctor_get(v_fst_3759_, 0);
                            crate::leanh::lean_inc(v_val_3760_);
                            crate::leanh::lean_dec_ref_known(v_fst_3759_, 1);
                            if crate::leanh::lean_obj_tag(v_val_3760_) == 0 {
                                state = 2;
                                continue;
                            } else {
                                v_val_3761_ = crate::leanh::lean_ctor_get(v_val_3760_, 0);
                                crate::leanh::lean_inc(v_val_3761_);
                                crate::leanh::lean_dec_ref_known(v_val_3760_, 1);
                                v___x_3762_ = lean_array_push(v_b_3721_, v_val_3761_);
                                v_a_3728_ = v___x_3762_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3721_);
                        crate::leanh::lean_dec(v_a_3720_);
                        crate::leanh::lean_dec(v_declName_3714_);
                        v_a_3763_ = crate::leanh::lean_ctor_get(v___x_3757_, 0);
                        v_isSharedCheck_3770_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3757_)) as u8;
                        if v_isSharedCheck_3770_ == 0 {
                            v___x_3765_ = v___x_3757_;
                            v_isShared_3766_ = v_isSharedCheck_3770_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3763_);
                            crate::leanh::lean_dec(v___x_3757_);
                            v___x_3765_ = crate::leanh::lean_box(0);
                            v_isShared_3766_ = v_isSharedCheck_3770_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3729_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3730_ = lean_nat_add(v_a_3720_, v___x_3729_);
                crate::leanh::lean_dec(v_a_3720_);
                v_a_3720_ = v___x_3730_;
                v_b_3721_ = v_a_3728_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3733_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
                v___x_3734_ = 0;
                crate::leanh::lean_inc(v_declName_3714_);
                v___x_3735_ = l_Lean_MessageData_ofConstName(v_declName_3714_, v___x_3734_);
                v___x_3736_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3736_, 0, v___x_3733_);
                crate::leanh::lean_ctor_set(v___x_3736_, 1, v___x_3735_);
                v___x_3737_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___closed__1);
                v___x_3738_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3738_, 0, v___x_3736_);
                crate::leanh::lean_ctor_set(v___x_3738_, 1, v___x_3737_);
                v___x_3739_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_3738_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
                if crate::leanh::lean_obj_tag(v___x_3739_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3739_, 1);
                    v_a_3728_ = v_b_3721_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3721_);
                    crate::leanh::lean_dec(v_a_3720_);
                    crate::leanh::lean_dec(v_declName_3714_);
                    v_a_3740_ = crate::leanh::lean_ctor_get(v___x_3739_, 0);
                    v_isSharedCheck_3747_ = (!crate::leanh::lean_is_exclusive(v___x_3739_)) as u8;
                    if v_isSharedCheck_3747_ == 0 {
                        v___x_3742_ = v___x_3739_;
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3740_);
                        crate::leanh::lean_dec(v___x_3739_);
                        v___x_3742_ = crate::leanh::lean_box(0);
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3743_ == 0 {
                    v___x_3745_ = v___x_3742_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
                    v___x_3745_ = v_reuseFailAlloc_3746_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3745_;
            }
            5 => {
                if v_isShared_3766_ == 0 {
                    v___x_3768_ = v___x_3765_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg___boxed(
    mut v_declName_3771_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3772_: *mut crate::leanh::LeanObject,
    mut v_majorPos_3773_: *mut crate::leanh::LeanObject,
    mut v_numIndices_3774_: *mut crate::leanh::LeanObject,
    mut v_xs_3775_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3776_: *mut crate::leanh::LeanObject,
    mut v_a_3777_: *mut crate::leanh::LeanObject,
    mut v_b_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3784_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_3771_, v_upperBound_3772_, v_majorPos_3773_, v_numIndices_3774_, v_xs_3775_, v_Iargs_3776_, v_a_3777_, v_b_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
    crate::leanh::lean_dec(v___y_3782_);
    crate::leanh::lean_dec_ref(v___y_3781_);
    crate::leanh::lean_dec(v___y_3780_);
    crate::leanh::lean_dec_ref(v___y_3779_);
    crate::leanh::lean_dec_ref(v_Iargs_3776_);
    crate::leanh::lean_dec_ref(v_xs_3775_);
    crate::leanh::lean_dec(v_numIndices_3774_);
    crate::leanh::lean_dec(v_majorPos_3773_);
    crate::leanh::lean_dec(v_upperBound_3772_);
    return v_res_3784_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(
    mut v_declName_3787_: *mut crate::leanh::LeanObject,
    mut v_xs_3788_: *mut crate::leanh::LeanObject,
    mut v_majorPos_3789_: *mut crate::leanh::LeanObject,
    mut v_numIndices_3790_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3791_: *mut crate::leanh::LeanObject,
    mut v_a_3792_: *mut crate::leanh::LeanObject,
    mut v_a_3793_: *mut crate::leanh::LeanObject,
    mut v_a_3794_: *mut crate::leanh::LeanObject,
    mut v_a_3795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3803_: u8 = 0;
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3808_: u8 = 0;
    let mut v_a_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3797_ = crate::leanh::lean_unsigned_to_nat(0);
                v_indicesPos_3798_ =
                    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___closed__0;
                v___x_3799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_3787_, v_numIndices_3790_, v_majorPos_3789_, v_numIndices_3790_, v_xs_3788_, v_Iargs_3791_, v___x_3797_, v_indicesPos_3798_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_);
                if crate::leanh::lean_obj_tag(v___x_3799_) == 0 {
                    v_a_3800_ = crate::leanh::lean_ctor_get(v___x_3799_, 0);
                    v_isSharedCheck_3808_ = (!crate::leanh::lean_is_exclusive(v___x_3799_)) as u8;
                    if v_isSharedCheck_3808_ == 0 {
                        v___x_3802_ = v___x_3799_;
                        v_isShared_3803_ = v_isSharedCheck_3808_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3800_);
                        crate::leanh::lean_dec(v___x_3799_);
                        v___x_3802_ = crate::leanh::lean_box(0);
                        v_isShared_3803_ = v_isSharedCheck_3808_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3809_ = crate::leanh::lean_ctor_get(v___x_3799_, 0);
                    v_isSharedCheck_3816_ = (!crate::leanh::lean_is_exclusive(v___x_3799_)) as u8;
                    if v_isSharedCheck_3816_ == 0 {
                        v___x_3811_ = v___x_3799_;
                        v_isShared_3812_ = v_isSharedCheck_3816_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3809_);
                        crate::leanh::lean_dec(v___x_3799_);
                        v___x_3811_ = crate::leanh::lean_box(0);
                        v_isShared_3812_ = v_isSharedCheck_3816_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3804_ = lean_array_to_list(v_a_3800_);
                if v_isShared_3803_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3802_, 0, v___x_3804_);
                    v___x_3806_ = v___x_3802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3807_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
                    v___x_3806_ = v_reuseFailAlloc_3807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3806_;
            }
            3 => {
                if v_isShared_3812_ == 0 {
                    v___x_3814_ = v___x_3811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
                    v___x_3814_ = v_reuseFailAlloc_3815_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___boxed(
    mut v_declName_3817_: *mut crate::leanh::LeanObject,
    mut v_xs_3818_: *mut crate::leanh::LeanObject,
    mut v_majorPos_3819_: *mut crate::leanh::LeanObject,
    mut v_numIndices_3820_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3821_: *mut crate::leanh::LeanObject,
    mut v_a_3822_: *mut crate::leanh::LeanObject,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
    mut v_a_3824_: *mut crate::leanh::LeanObject,
    mut v_a_3825_: *mut crate::leanh::LeanObject,
    mut v_a_3826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3827_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(
        v_declName_3817_,
        v_xs_3818_,
        v_majorPos_3819_,
        v_numIndices_3820_,
        v_Iargs_3821_,
        v_a_3822_,
        v_a_3823_,
        v_a_3824_,
        v_a_3825_,
    );
    crate::leanh::lean_dec(v_a_3825_);
    crate::leanh::lean_dec_ref(v_a_3824_);
    crate::leanh::lean_dec(v_a_3823_);
    crate::leanh::lean_dec_ref(v_a_3822_);
    crate::leanh::lean_dec_ref(v_Iargs_3821_);
    crate::leanh::lean_dec(v_numIndices_3820_);
    crate::leanh::lean_dec(v_majorPos_3819_);
    crate::leanh::lean_dec_ref(v_xs_3818_);
    return v_res_3827_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(
    mut v_declName_3828_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3829_: *mut crate::leanh::LeanObject,
    mut v_majorPos_3830_: *mut crate::leanh::LeanObject,
    mut v_numIndices_3831_: *mut crate::leanh::LeanObject,
    mut v_xs_3832_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3833_: *mut crate::leanh::LeanObject,
    mut v_inst_3834_: *mut crate::leanh::LeanObject,
    mut v_R_3835_: *mut crate::leanh::LeanObject,
    mut v_a_3836_: *mut crate::leanh::LeanObject,
    mut v_b_3837_: *mut crate::leanh::LeanObject,
    mut v_c_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
    mut v___y_3841_: *mut crate::leanh::LeanObject,
    mut v___y_3842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3844_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___redArg(v_declName_3828_, v_upperBound_3829_, v_majorPos_3830_, v_numIndices_3831_, v_xs_3832_, v_Iargs_3833_, v_a_3836_, v_b_3837_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
    return v___x_3844_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0___boxed(
    mut v_declName_3845_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3846_: *mut crate::leanh::LeanObject,
    mut v_majorPos_3847_: *mut crate::leanh::LeanObject,
    mut v_numIndices_3848_: *mut crate::leanh::LeanObject,
    mut v_xs_3849_: *mut crate::leanh::LeanObject,
    mut v_Iargs_3850_: *mut crate::leanh::LeanObject,
    mut v_inst_3851_: *mut crate::leanh::LeanObject,
    mut v_R_3852_: *mut crate::leanh::LeanObject,
    mut v_a_3853_: *mut crate::leanh::LeanObject,
    mut v_b_3854_: *mut crate::leanh::LeanObject,
    mut v_c_3855_: *mut crate::leanh::LeanObject,
    mut v___y_3856_: *mut crate::leanh::LeanObject,
    mut v___y_3857_: *mut crate::leanh::LeanObject,
    mut v___y_3858_: *mut crate::leanh::LeanObject,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos_spec__0(v_declName_3845_, v_upperBound_3846_, v_majorPos_3847_, v_numIndices_3848_, v_xs_3849_, v_Iargs_3850_, v_inst_3851_, v_R_3852_, v_a_3853_, v_b_3854_, v_c_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
    crate::leanh::lean_dec(v___y_3859_);
    crate::leanh::lean_dec_ref(v___y_3858_);
    crate::leanh::lean_dec(v___y_3857_);
    crate::leanh::lean_dec_ref(v___y_3856_);
    crate::leanh::lean_dec_ref(v_Iargs_3850_);
    crate::leanh::lean_dec_ref(v_xs_3849_);
    crate::leanh::lean_dec(v_numIndices_3848_);
    crate::leanh::lean_dec(v_majorPos_3847_);
    crate::leanh::lean_dec(v_upperBound_3846_);
    return v_res_3861_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3863_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__0;
    v___x_3864_ = l_Lean_stringToMessageData(v___x_3863_);
    return v___x_3864_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(
    mut v_declName_3865_: *mut crate::leanh::LeanObject,
    mut v_motiveResultType_3866_: *mut crate::leanh::LeanObject,
    mut v_a_3867_: *mut crate::leanh::LeanObject,
    mut v_a_3868_: *mut crate::leanh::LeanObject,
    mut v_a_3869_: *mut crate::leanh::LeanObject,
    mut v_a_3870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: u8 = 0;
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_motiveResultType_3866_) == 3 {
                    v_u_3884_ = crate::leanh::lean_ctor_get(v_motiveResultType_3866_, 0);
                    match crate::leanh::lean_obj_tag(v_u_3884_) {
                        0 => {
                            crate::leanh::lean_dec(v_declName_3865_);
                            v___x_3885_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3885_, 0, v_u_3884_);
                            return v___x_3885_;
                        }
                        4 => {
                            crate::leanh::lean_dec(v_declName_3865_);
                            crate::leanh::lean_inc_ref(v_u_3884_);
                            v___x_3886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3886_, 0, v_u_3884_);
                            return v___x_3886_;
                        }
                        _ => {
                            v___y_3873_ = v_a_3867_;
                            v___y_3874_ = v_a_3868_;
                            v___y_3875_ = v_a_3869_;
                            v___y_3876_ = v_a_3870_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___y_3873_ = v_a_3867_;
                    v___y_3874_ = v_a_3868_;
                    v___y_3875_ = v_a_3869_;
                    v___y_3876_ = v_a_3870_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3877_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
                v___x_3878_ = 0;
                v___x_3879_ = l_Lean_MessageData_ofConstName(v_declName_3865_, v___x_3878_);
                v___x_3880_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3880_, 0, v___x_3877_);
                crate::leanh::lean_ctor_set(v___x_3880_, 1, v___x_3879_);
                v___x_3881_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1);
                v___x_3882_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3880_);
                crate::leanh::lean_ctor_set(v___x_3882_, 1, v___x_3881_);
                v___x_3883_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_3882_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
                return v___x_3883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___boxed(
    mut v_declName_3887_: *mut crate::leanh::LeanObject,
    mut v_motiveResultType_3888_: *mut crate::leanh::LeanObject,
    mut v_a_3889_: *mut crate::leanh::LeanObject,
    mut v_a_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3894_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(
        v_declName_3887_,
        v_motiveResultType_3888_,
        v_a_3889_,
        v_a_3890_,
        v_a_3891_,
        v_a_3892_,
    );
    crate::leanh::lean_dec(v_a_3892_);
    crate::leanh::lean_dec_ref(v_a_3891_);
    crate::leanh::lean_dec(v_a_3890_);
    crate::leanh::lean_dec_ref(v_a_3889_);
    crate::leanh::lean_dec_ref(v_motiveResultType_3888_);
    return v_res_3894_;
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(
    mut v___x_3895_: *mut crate::leanh::LeanObject,
    mut v_as_3896_: *mut crate::leanh::LeanObject,
    mut v_j_3897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: u8 = 0;
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3898_ = lean_array_get_size(v_as_3896_);
                v___x_3899_ = lean_nat_dec_lt(v_j_3897_, v___x_3898_);
                if v___x_3899_ == 0 {
                    crate::leanh::lean_dec(v_j_3897_);
                    v___x_3900_ = crate::leanh::lean_box(0);
                    return v___x_3900_;
                } else {
                    v___x_3901_ = lean_array_fget_borrowed(v_as_3896_, v_j_3897_);
                    v___x_3902_ = lean_level_eq(v___x_3901_, v___x_3895_);
                    if v___x_3902_ == 0 {
                        v___x_3903_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3904_ = lean_nat_add(v_j_3897_, v___x_3903_);
                        crate::leanh::lean_dec(v_j_3897_);
                        v_j_3897_ = v___x_3904_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3906_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3906_, 0, v_j_3897_);
                        return v___x_3906_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0___boxed(
    mut v___x_3907_: *mut crate::leanh::LeanObject,
    mut v_as_3908_: *mut crate::leanh::LeanObject,
    mut v_j_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3910_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(v___x_3907_, v_as_3908_, v_j_3909_);
    crate::leanh::lean_dec_ref(v_as_3908_);
    crate::leanh::lean_dec(v___x_3907_);
    return v_res_3910_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3912_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__0;
    v___x_3913_ = l_Lean_stringToMessageData(v___x_3912_);
    return v___x_3913_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(
    mut v_motiveLvl_3914_: *mut crate::leanh::LeanObject,
    mut v_Ilevels_3915_: *mut crate::leanh::LeanObject,
    mut v_declName_3916_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3917_: *mut crate::leanh::LeanObject,
    mut v_b_3918_: *mut crate::leanh::LeanObject,
    mut v___y_3919_: *mut crate::leanh::LeanObject,
    mut v___y_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3944_: u8 = 0;
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3948_: u8 = 0;
    let mut v_val_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3952_: u8 = 0;
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3917_) == 0 {
                    crate::leanh::lean_dec(v_declName_3916_);
                    v___x_3924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3924_, 0, v_b_3918_);
                    return v___x_3924_;
                } else {
                    v_head_3925_ = crate::leanh::lean_ctor_get(v_as_x27_3917_, 0);
                    v_tail_3926_ = crate::leanh::lean_ctor_get(v_as_x27_3917_, 1);
                    crate::leanh::lean_inc(v_head_3925_);
                    v___x_3927_ = l_Lean_mkLevelParam(v_head_3925_);
                    v___x_3928_ = lean_level_eq(v_motiveLvl_3914_, v___x_3927_);
                    if v___x_3928_ == 0 {
                        v___x_3929_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3930_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__0(v___x_3927_, v_Ilevels_3915_, v___x_3929_);
                        crate::leanh::lean_dec(v___x_3927_);
                        if crate::leanh::lean_obj_tag(v___x_3930_) == 0 {
                            crate::leanh::lean_dec_ref(v_b_3918_);
                            v___x_3931_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
                            v___x_3932_ =
                                l_Lean_MessageData_ofConstName(v_declName_3916_, v___x_3928_);
                            v___x_3933_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3933_, 0, v___x_3931_);
                            crate::leanh::lean_ctor_set(v___x_3933_, 1, v___x_3932_);
                            v___x_3934_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___closed__1);
                            v___x_3935_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3935_, 0, v___x_3933_);
                            crate::leanh::lean_ctor_set(v___x_3935_, 1, v___x_3934_);
                            crate::leanh::lean_inc(v_head_3925_);
                            v___x_3936_ = l_Lean_MessageData_ofName(v_head_3925_);
                            v___x_3937_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3937_, 0, v___x_3935_);
                            crate::leanh::lean_ctor_set(v___x_3937_, 1, v___x_3936_);
                            v___x_3938_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
                            v___x_3939_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3939_, 0, v___x_3937_);
                            crate::leanh::lean_ctor_set(v___x_3939_, 1, v___x_3938_);
                            v___x_3940_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_3939_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
                            v_a_3941_ = crate::leanh::lean_ctor_get(v___x_3940_, 0);
                            v_isSharedCheck_3948_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3940_)) as u8;
                            if v_isSharedCheck_3948_ == 0 {
                                v___x_3943_ = v___x_3940_;
                                v_isShared_3944_ = v_isSharedCheck_3948_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3941_);
                                crate::leanh::lean_dec(v___x_3940_);
                                v___x_3943_ = crate::leanh::lean_box(0);
                                v_isShared_3944_ = v_isSharedCheck_3948_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_val_3949_ = crate::leanh::lean_ctor_get(v___x_3930_, 0);
                            v_isSharedCheck_3958_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3930_)) as u8;
                            if v_isSharedCheck_3958_ == 0 {
                                v___x_3951_ = v___x_3930_;
                                v_isShared_3952_ = v_isSharedCheck_3958_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_3949_);
                                crate::leanh::lean_dec(v___x_3930_);
                                v___x_3951_ = crate::leanh::lean_box(0);
                                v_isShared_3952_ = v_isSharedCheck_3958_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3927_);
                        v___x_3959_ = crate::leanh::lean_box(0);
                        v___x_3960_ = lean_array_push(v_b_3918_, v___x_3959_);
                        v_as_x27_3917_ = v_tail_3926_;
                        v_b_3918_ = v___x_3960_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3944_ == 0 {
                    v___x_3946_ = v___x_3943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
                    v___x_3946_ = v_reuseFailAlloc_3947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3946_;
            }
            3 => {
                if v_isShared_3952_ == 0 {
                    v___x_3954_ = v___x_3951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3957_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_val_3949_);
                    v___x_3954_ = v_reuseFailAlloc_3957_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3955_ = lean_array_push(v_b_3918_, v___x_3954_);
                v_as_x27_3917_ = v_tail_3926_;
                v_b_3918_ = v___x_3955_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg___boxed(
    mut v_motiveLvl_3962_: *mut crate::leanh::LeanObject,
    mut v_Ilevels_3963_: *mut crate::leanh::LeanObject,
    mut v_declName_3964_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3965_: *mut crate::leanh::LeanObject,
    mut v_b_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
    mut v___y_3968_: *mut crate::leanh::LeanObject,
    mut v___y_3969_: *mut crate::leanh::LeanObject,
    mut v___y_3970_: *mut crate::leanh::LeanObject,
    mut v___y_3971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3972_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_3962_, v_Ilevels_3963_, v_declName_3964_, v_as_x27_3965_, v_b_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
    crate::leanh::lean_dec(v___y_3970_);
    crate::leanh::lean_dec_ref(v___y_3969_);
    crate::leanh::lean_dec(v___y_3968_);
    crate::leanh::lean_dec_ref(v___y_3967_);
    crate::leanh::lean_dec(v_as_x27_3965_);
    crate::leanh::lean_dec_ref(v_Ilevels_3963_);
    crate::leanh::lean_dec(v_motiveLvl_3962_);
    return v_res_3972_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(
    mut v_declName_3975_: *mut crate::leanh::LeanObject,
    mut v_lparams_3976_: *mut crate::leanh::LeanObject,
    mut v_motiveLvl_3977_: *mut crate::leanh::LeanObject,
    mut v_Ilevels_3978_: *mut crate::leanh::LeanObject,
    mut v_a_3979_: *mut crate::leanh::LeanObject,
    mut v_a_3980_: *mut crate::leanh::LeanObject,
    mut v_a_3981_: *mut crate::leanh::LeanObject,
    mut v_a_3982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_Ilevels_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univLevelPos_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut v_a_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_Ilevels_3984_ = lean_array_mk(v_Ilevels_3978_);
                v_univLevelPos_3985_ =
                    l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___closed__0;
                v___x_3986_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_3977_, v_Ilevels_3984_, v_declName_3975_, v_lparams_3976_, v_univLevelPos_3985_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_);
                crate::leanh::lean_dec_ref(v_Ilevels_3984_);
                if crate::leanh::lean_obj_tag(v___x_3986_) == 0 {
                    v_a_3987_ = crate::leanh::lean_ctor_get(v___x_3986_, 0);
                    v_isSharedCheck_3995_ = (!crate::leanh::lean_is_exclusive(v___x_3986_)) as u8;
                    if v_isSharedCheck_3995_ == 0 {
                        v___x_3989_ = v___x_3986_;
                        v_isShared_3990_ = v_isSharedCheck_3995_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3987_);
                        crate::leanh::lean_dec(v___x_3986_);
                        v___x_3989_ = crate::leanh::lean_box(0);
                        v_isShared_3990_ = v_isSharedCheck_3995_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3996_ = crate::leanh::lean_ctor_get(v___x_3986_, 0);
                    v_isSharedCheck_4003_ = (!crate::leanh::lean_is_exclusive(v___x_3986_)) as u8;
                    if v_isSharedCheck_4003_ == 0 {
                        v___x_3998_ = v___x_3986_;
                        v_isShared_3999_ = v_isSharedCheck_4003_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3996_);
                        crate::leanh::lean_dec(v___x_3986_);
                        v___x_3998_ = crate::leanh::lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4003_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3991_ = lean_array_to_list(v_a_3987_);
                if v_isShared_3990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3989_, 0, v___x_3991_);
                    v___x_3993_ = v___x_3989_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3994_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
                    v___x_3993_ = v_reuseFailAlloc_3994_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3993_;
            }
            3 => {
                if v_isShared_3999_ == 0 {
                    v___x_4001_ = v___x_3998_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
                    v___x_4001_ = v_reuseFailAlloc_4002_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___boxed(
    mut v_declName_4004_: *mut crate::leanh::LeanObject,
    mut v_lparams_4005_: *mut crate::leanh::LeanObject,
    mut v_motiveLvl_4006_: *mut crate::leanh::LeanObject,
    mut v_Ilevels_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
    mut v_a_4009_: *mut crate::leanh::LeanObject,
    mut v_a_4010_: *mut crate::leanh::LeanObject,
    mut v_a_4011_: *mut crate::leanh::LeanObject,
    mut v_a_4012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4013_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(
        v_declName_4004_,
        v_lparams_4005_,
        v_motiveLvl_4006_,
        v_Ilevels_4007_,
        v_a_4008_,
        v_a_4009_,
        v_a_4010_,
        v_a_4011_,
    );
    crate::leanh::lean_dec(v_a_4011_);
    crate::leanh::lean_dec_ref(v_a_4010_);
    crate::leanh::lean_dec(v_a_4009_);
    crate::leanh::lean_dec_ref(v_a_4008_);
    crate::leanh::lean_dec(v_motiveLvl_4006_);
    crate::leanh::lean_dec(v_lparams_4005_);
    return v_res_4013_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(
    mut v_motiveLvl_4014_: *mut crate::leanh::LeanObject,
    mut v_Ilevels_4015_: *mut crate::leanh::LeanObject,
    mut v_declName_4016_: *mut crate::leanh::LeanObject,
    mut v_as_4017_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4018_: *mut crate::leanh::LeanObject,
    mut v_b_4019_: *mut crate::leanh::LeanObject,
    mut v_a_4020_: *mut crate::leanh::LeanObject,
    mut v___y_4021_: *mut crate::leanh::LeanObject,
    mut v___y_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4026_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___redArg(v_motiveLvl_4014_, v_Ilevels_4015_, v_declName_4016_, v_as_x27_4018_, v_b_4019_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
    return v___x_4026_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1___boxed(
    mut v_motiveLvl_4027_: *mut crate::leanh::LeanObject,
    mut v_Ilevels_4028_: *mut crate::leanh::LeanObject,
    mut v_declName_4029_: *mut crate::leanh::LeanObject,
    mut v_as_4030_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4031_: *mut crate::leanh::LeanObject,
    mut v_b_4032_: *mut crate::leanh::LeanObject,
    mut v_a_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
    mut v___y_4036_: *mut crate::leanh::LeanObject,
    mut v___y_4037_: *mut crate::leanh::LeanObject,
    mut v___y_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos_spec__1(v_motiveLvl_4027_, v_Ilevels_4028_, v_declName_4029_, v_as_4030_, v_as_x27_4031_, v_b_4032_, v_a_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
    crate::leanh::lean_dec(v___y_4037_);
    crate::leanh::lean_dec_ref(v___y_4036_);
    crate::leanh::lean_dec(v___y_4035_);
    crate::leanh::lean_dec_ref(v___y_4034_);
    crate::leanh::lean_dec(v_as_x27_4031_);
    crate::leanh::lean_dec(v_as_4030_);
    crate::leanh::lean_dec_ref(v_Ilevels_4028_);
    crate::leanh::lean_dec(v_motiveLvl_4027_);
    return v_res_4039_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(
    mut v_k_4040_: *mut crate::leanh::LeanObject,
    mut v_b_4041_: *mut crate::leanh::LeanObject,
    mut v_c_4042_: *mut crate::leanh::LeanObject,
    mut v___y_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4046_);
    crate::leanh::lean_inc_ref(v___y_4045_);
    crate::leanh::lean_inc(v___y_4044_);
    crate::leanh::lean_inc_ref(v___y_4043_);
    v___x_4048_ = crate::leanh::lean_apply_7(
        v_k_4040_,
        v_b_4041_,
        v_c_4042_,
        v___y_4043_,
        v___y_4044_,
        v___y_4045_,
        v___y_4046_,
        crate::leanh::lean_box(0),
    );
    return v___x_4048_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0___boxed(
    mut v_k_4049_: *mut crate::leanh::LeanObject,
    mut v_b_4050_: *mut crate::leanh::LeanObject,
    mut v_c_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4057_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0(v_k_4049_, v_b_4050_, v_c_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
    crate::leanh::lean_dec(v___y_4055_);
    crate::leanh::lean_dec_ref(v___y_4054_);
    crate::leanh::lean_dec(v___y_4053_);
    crate::leanh::lean_dec_ref(v___y_4052_);
    return v_res_4057_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(
    mut v_type_4058_: *mut crate::leanh::LeanObject,
    mut v_k_4059_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4060_: u8,
    mut v_whnfType_4061_: u8,
    mut v___y_4062_: *mut crate::leanh::LeanObject,
    mut v___y_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4072_: u8 = 0;
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4076_: u8 = 0;
    let mut v_a_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4080_: u8 = 0;
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4067_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_4067_, 0, v_k_4059_);
                v___x_4068_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_4058_,
                    v___f_4067_,
                    v_cleanupAnnotations_4060_,
                    v_whnfType_4061_,
                    v___y_4062_,
                    v___y_4063_,
                    v___y_4064_,
                    v___y_4065_,
                );
                if crate::leanh::lean_obj_tag(v___x_4068_) == 0 {
                    v_a_4069_ = crate::leanh::lean_ctor_get(v___x_4068_, 0);
                    v_isSharedCheck_4076_ = (!crate::leanh::lean_is_exclusive(v___x_4068_)) as u8;
                    if v_isSharedCheck_4076_ == 0 {
                        v___x_4071_ = v___x_4068_;
                        v_isShared_4072_ = v_isSharedCheck_4076_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4069_);
                        crate::leanh::lean_dec(v___x_4068_);
                        v___x_4071_ = crate::leanh::lean_box(0);
                        v_isShared_4072_ = v_isSharedCheck_4076_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4077_ = crate::leanh::lean_ctor_get(v___x_4068_, 0);
                    v_isSharedCheck_4084_ = (!crate::leanh::lean_is_exclusive(v___x_4068_)) as u8;
                    if v_isSharedCheck_4084_ == 0 {
                        v___x_4079_ = v___x_4068_;
                        v_isShared_4080_ = v_isSharedCheck_4084_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4077_);
                        crate::leanh::lean_dec(v___x_4068_);
                        v___x_4079_ = crate::leanh::lean_box(0);
                        v_isShared_4080_ = v_isSharedCheck_4084_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4072_ == 0 {
                    v___x_4074_ = v___x_4071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
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
                    v___x_4082_ = v___x_4079_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
                    v___x_4082_ = v_reuseFailAlloc_4083_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg___boxed(
    mut v_type_4085_: *mut crate::leanh::LeanObject,
    mut v_k_4086_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4087_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4088_: *mut crate::leanh::LeanObject,
    mut v___y_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4094_: u8 = 0;
    let mut v_whnfType_boxed_4095_: u8 = 0;
    let mut v_res_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4094_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4087_) as u8);
    v_whnfType_boxed_4095_ = (crate::leanh::lean_unbox(v_whnfType_4088_) as u8);
    v_res_4096_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_type_4085_, v_k_4086_, v_cleanupAnnotations_boxed_4094_, v_whnfType_boxed_4095_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
    crate::leanh::lean_dec(v___y_4092_);
    crate::leanh::lean_dec_ref(v___y_4091_);
    crate::leanh::lean_dec(v___y_4090_);
    crate::leanh::lean_dec_ref(v___y_4089_);
    return v_res_4096_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(
    mut v_00_u03b1_4097_: *mut crate::leanh::LeanObject,
    mut v_type_4098_: *mut crate::leanh::LeanObject,
    mut v_k_4099_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4100_: u8,
    mut v_whnfType_4101_: u8,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4107_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_type_4098_, v_k_4099_, v_cleanupAnnotations_4100_, v_whnfType_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
    return v___x_4107_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___boxed(
    mut v_00_u03b1_4108_: *mut crate::leanh::LeanObject,
    mut v_type_4109_: *mut crate::leanh::LeanObject,
    mut v_k_4110_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4111_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4118_: u8 = 0;
    let mut v_whnfType_boxed_4119_: u8 = 0;
    let mut v_res_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4118_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4111_) as u8);
    v_whnfType_boxed_4119_ = (crate::leanh::lean_unbox(v_whnfType_4112_) as u8);
    v_res_4120_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2(v_00_u03b1_4108_, v_type_4109_, v_k_4110_, v_cleanupAnnotations_boxed_4118_, v_whnfType_boxed_4119_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
    crate::leanh::lean_dec(v___y_4116_);
    crate::leanh::lean_dec_ref(v___y_4115_);
    crate::leanh::lean_dec(v___y_4114_);
    crate::leanh::lean_dec_ref(v___y_4113_);
    return v_res_4120_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(
    mut v_motive_4121_: *mut crate::leanh::LeanObject,
    mut v_e_4122_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4123_: u8 = 0;
    v___x_4123_ = lean_expr_eqv(v_e_4122_, v_motive_4121_);
    return v___x_4123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0___boxed(
    mut v_motive_4124_: *mut crate::leanh::LeanObject,
    mut v_e_4125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4126_: u8 = 0;
    let mut v_r_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4126_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0(v_motive_4124_, v_e_4125_);
    crate::leanh::lean_dec_ref(v_e_4125_);
    crate::leanh::lean_dec_ref(v_motive_4124_);
    v_r_4127_ = crate::leanh::lean_box((v_res_4126_) as usize);
    return v_r_4127_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(
    mut v_motive_4128_: *mut crate::leanh::LeanObject,
    mut v___x_4129_: u8,
    mut v_as_4130_: *mut crate::leanh::LeanObject,
    mut v_i_4131_: usize,
    mut v_stop_4132_: usize,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4138_: u8 = 0;
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___f_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: u8 = 0;
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: usize = 0;
    let mut v___x_4149_: usize = 0;
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4159_: u8 = 0;
    let mut v_a_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4163_: u8 = 0;
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4167_: u8 = 0;
    let mut v___x_4168_: u8 = 0;
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4138_ = lean_usize_dec_eq(v_i_4131_, v_stop_4132_);
                if v___x_4138_ == 0 {
                    v___x_4139_ = lean_array_uget_borrowed(v_as_4130_, v_i_4131_);
                    crate::leanh::lean_inc(v___y_4136_);
                    crate::leanh::lean_inc_ref(v___y_4135_);
                    crate::leanh::lean_inc(v___y_4134_);
                    crate::leanh::lean_inc_ref(v___y_4133_);
                    crate::leanh::lean_inc(v___x_4139_);
                    v___x_4140_ = lean_infer_type(
                        v___x_4139_,
                        v___y_4133_,
                        v___y_4134_,
                        v___y_4135_,
                        v___y_4136_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4140_) == 0 {
                        v_a_4141_ = crate::leanh::lean_ctor_get(v___x_4140_, 0);
                        v_isSharedCheck_4159_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4140_)) as u8;
                        if v_isSharedCheck_4159_ == 0 {
                            v___x_4143_ = v___x_4140_;
                            v_isShared_4144_ = v_isSharedCheck_4159_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4141_);
                            crate::leanh::lean_dec(v___x_4140_);
                            v___x_4143_ = crate::leanh::lean_box(0);
                            v_isShared_4144_ = v_isSharedCheck_4159_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_motive_4128_);
                        v_a_4160_ = crate::leanh::lean_ctor_get(v___x_4140_, 0);
                        v_isSharedCheck_4167_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4140_)) as u8;
                        if v_isSharedCheck_4167_ == 0 {
                            v___x_4162_ = v___x_4140_;
                            v_isShared_4163_ = v_isSharedCheck_4167_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4160_);
                            crate::leanh::lean_dec(v___x_4140_);
                            v___x_4162_ = crate::leanh::lean_box(0);
                            v_isShared_4163_ = v_isSharedCheck_4167_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_motive_4128_);
                    v___x_4168_ = 0;
                    v___x_4169_ = crate::leanh::lean_box((v___x_4168_) as usize);
                    v___x_4170_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4170_, 0, v___x_4169_);
                    return v___x_4170_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_motive_4128_);
                v___f_4145_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_4145_, 0, v_motive_4128_);
                v___x_4146_ = 1;
                v___x_4147_ = lean_find_expr(v___f_4145_, v_a_4141_);
                crate::leanh::lean_dec(v_a_4141_);
                crate::leanh::lean_dec_ref(v___f_4145_);
                if crate::leanh::lean_obj_tag(v___x_4147_) == 0 {
                    if v___x_4129_ == 0 {
                        crate::leanh::lean_del_object(v___x_4143_);
                        v___x_4148_ = 1usize;
                        v___x_4149_ = lean_usize_add(v_i_4131_, v___x_4148_);
                        v_i_4131_ = v___x_4149_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_motive_4128_);
                        v___x_4151_ = crate::leanh::lean_box((v___x_4146_) as usize);
                        if v_isShared_4144_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4143_, 0, v___x_4151_);
                            v___x_4153_ = v___x_4143_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4154_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4151_);
                            v___x_4153_ = v_reuseFailAlloc_4154_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_4147_, 1);
                    crate::leanh::lean_dec_ref(v_motive_4128_);
                    v___x_4155_ = crate::leanh::lean_box((v___x_4146_) as usize);
                    if v_isShared_4144_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4143_, 0, v___x_4155_);
                        v___x_4157_ = v___x_4143_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4158_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
                        v___x_4157_ = v_reuseFailAlloc_4158_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4153_;
            }
            3 => {
                return v___x_4157_;
            }
            4 => {
                if v_isShared_4163_ == 0 {
                    v___x_4165_ = v___x_4162_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
                    v___x_4165_ = v_reuseFailAlloc_4166_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0___boxed(
    mut v_motive_4171_: *mut crate::leanh::LeanObject,
    mut v___x_4172_: *mut crate::leanh::LeanObject,
    mut v_as_4173_: *mut crate::leanh::LeanObject,
    mut v_i_4174_: *mut crate::leanh::LeanObject,
    mut v_stop_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4143__boxed_4181_: u8 = 0;
    let mut v_i_boxed_4182_: usize = 0;
    let mut v_stop_boxed_4183_: usize = 0;
    let mut v_res_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4143__boxed_4181_ = (crate::leanh::lean_unbox(v___x_4172_) as u8);
    v_i_boxed_4182_ = crate::leanh::lean_unbox_usize(v_i_4174_);
    crate::leanh::lean_dec(v_i_4174_);
    v_stop_boxed_4183_ = crate::leanh::lean_unbox_usize(v_stop_4175_);
    crate::leanh::lean_dec(v_stop_4175_);
    v_res_4184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(v_motive_4171_, v___x_4143__boxed_4181_, v_as_4173_, v_i_boxed_4182_, v_stop_boxed_4183_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
    crate::leanh::lean_dec(v___y_4179_);
    crate::leanh::lean_dec_ref(v___y_4178_);
    crate::leanh::lean_dec(v___y_4177_);
    crate::leanh::lean_dec_ref(v___y_4176_);
    crate::leanh::lean_dec_ref(v_as_4173_);
    return v_res_4184_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(
    mut v_motive_4185_: *mut crate::leanh::LeanObject,
    mut v___x_4186_: *mut crate::leanh::LeanObject,
    mut v___x_4187_: u8,
    mut v_minorArgs_4188_: *mut crate::leanh::LeanObject,
    mut v_x_4189_: *mut crate::leanh::LeanObject,
    mut v_x_4190_: *mut crate::leanh::LeanObject,
    mut v_x_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: u8 = 0;
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursor_4207_: u8 = 0;
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: u8 = 0;
    let mut v___x_4214_: usize = 0;
    let mut v___x_4215_: usize = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: u8 = 0;
    let mut v_a_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4222_: u8 = 0;
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4189_) == 5 {
                    v_fn_4197_ = crate::leanh::lean_ctor_get(v_x_4189_, 0);
                    crate::leanh::lean_inc_ref(v_fn_4197_);
                    v_arg_4198_ = crate::leanh::lean_ctor_get(v_x_4189_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4198_);
                    crate::leanh::lean_dec_ref_known(v_x_4189_, 2);
                    v___x_4199_ = lean_array_set(v_x_4190_, v_x_4191_, v_arg_4198_);
                    v___x_4200_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4201_ = lean_nat_sub(v_x_4191_, v___x_4200_);
                    crate::leanh::lean_dec(v_x_4191_);
                    v_x_4189_ = v_fn_4197_;
                    v_x_4190_ = v___x_4199_;
                    v_x_4191_ = v___x_4201_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_4191_);
                    crate::leanh::lean_dec_ref(v_x_4190_);
                    v___x_4203_ = lean_expr_eqv(v_x_4189_, v_motive_4185_);
                    crate::leanh::lean_dec_ref(v_x_4189_);
                    v___x_4204_ = crate::leanh::lean_box((v___x_4203_) as usize);
                    v___x_4205_ = lean_array_push(v___x_4186_, v___x_4204_);
                    if v___x_4187_ == 0 {
                        v___x_4211_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4212_ = lean_array_get_size(v_minorArgs_4188_);
                        v___x_4213_ = lean_nat_dec_lt(v___x_4211_, v___x_4212_);
                        if v___x_4213_ == 0 {
                            crate::leanh::lean_dec_ref(v_motive_4185_);
                            v_recursor_4207_ = v___x_4187_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_4213_ == 0 {
                                crate::leanh::lean_dec_ref(v_motive_4185_);
                                v_recursor_4207_ = v___x_4187_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4214_ = 0usize;
                                v___x_4215_ = lean_usize_of_nat(v___x_4212_);
                                v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__0(v_motive_4185_, v___x_4187_, v_minorArgs_4188_, v___x_4214_, v___x_4215_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
                                if crate::leanh::lean_obj_tag(v___x_4216_) == 0 {
                                    v_a_4217_ = crate::leanh::lean_ctor_get(v___x_4216_, 0);
                                    crate::leanh::lean_inc(v_a_4217_);
                                    crate::leanh::lean_dec_ref_known(v___x_4216_, 1);
                                    v___x_4218_ = (crate::leanh::lean_unbox(v_a_4217_) as u8);
                                    crate::leanh::lean_dec(v_a_4217_);
                                    v_recursor_4207_ = v___x_4218_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4205_);
                                    v_a_4219_ = crate::leanh::lean_ctor_get(v___x_4216_, 0);
                                    v_isSharedCheck_4226_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4216_)) as u8;
                                    if v_isSharedCheck_4226_ == 0 {
                                        v___x_4221_ = v___x_4216_;
                                        v_isShared_4222_ = v_isSharedCheck_4226_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4219_);
                                        crate::leanh::lean_dec(v___x_4216_);
                                        v___x_4221_ = crate::leanh::lean_box(0);
                                        v_isShared_4222_ = v_isSharedCheck_4226_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_motive_4185_);
                        v_recursor_4207_ = v___x_4187_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4208_ = crate::leanh::lean_box((v_recursor_4207_) as usize);
                v___x_4209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4209_, 0, v___x_4205_);
                crate::leanh::lean_ctor_set(v___x_4209_, 1, v___x_4208_);
                v___x_4210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4210_, 0, v___x_4209_);
                return v___x_4210_;
            }
            2 => {
                if v_isShared_4222_ == 0 {
                    v___x_4224_ = v___x_4221_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4225_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
                    v___x_4224_ = v_reuseFailAlloc_4225_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1___boxed(
    mut v_motive_4227_: *mut crate::leanh::LeanObject,
    mut v___x_4228_: *mut crate::leanh::LeanObject,
    mut v___x_4229_: *mut crate::leanh::LeanObject,
    mut v_minorArgs_4230_: *mut crate::leanh::LeanObject,
    mut v_x_4231_: *mut crate::leanh::LeanObject,
    mut v_x_4232_: *mut crate::leanh::LeanObject,
    mut v_x_4233_: *mut crate::leanh::LeanObject,
    mut v___y_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4229__boxed_4239_: u8 = 0;
    let mut v_res_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4229__boxed_4239_ = (crate::leanh::lean_unbox(v___x_4229_) as u8);
    v_res_4240_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(v_motive_4227_, v___x_4228_, v___x_4229__boxed_4239_, v_minorArgs_4230_, v_x_4231_, v_x_4232_, v_x_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
    crate::leanh::lean_dec(v___y_4237_);
    crate::leanh::lean_dec_ref(v___y_4236_);
    crate::leanh::lean_dec(v___y_4235_);
    crate::leanh::lean_dec_ref(v___y_4234_);
    crate::leanh::lean_dec_ref(v_minorArgs_4230_);
    return v_res_4240_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4241_ = crate::leanh::lean_box(0);
    v_dummy_4242_ = l_Lean_Expr_sort___override(v___x_4241_);
    return v_dummy_4242_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(
    mut v_motive_4243_: *mut crate::leanh::LeanObject,
    mut v_fst_4244_: *mut crate::leanh::LeanObject,
    mut v_snd_4245_: *mut crate::leanh::LeanObject,
    mut v_minorArgs_4246_: *mut crate::leanh::LeanObject,
    mut v_minorResultType_4247_: *mut crate::leanh::LeanObject,
    mut v___y_4248_: *mut crate::leanh::LeanObject,
    mut v___y_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
    mut v___y_4251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_4253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
    v_nargs_4254_ = l_Lean_Expr_getAppNumArgs(v_minorResultType_4247_);
    crate::leanh::lean_inc(v_nargs_4254_);
    v___x_4255_ = lean_mk_array(v_nargs_4254_, v_dummy_4253_);
    v___x_4256_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4257_ = lean_nat_sub(v_nargs_4254_, v___x_4256_);
    crate::leanh::lean_dec(v_nargs_4254_);
    v___x_4258_ = (crate::leanh::lean_unbox(v_snd_4245_) as u8);
    v___x_4259_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__1(v_motive_4243_, v_fst_4244_, v___x_4258_, v_minorArgs_4246_, v_minorResultType_4247_, v___x_4255_, v___x_4257_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
    return v___x_4259_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed(
    mut v_motive_4260_: *mut crate::leanh::LeanObject,
    mut v_fst_4261_: *mut crate::leanh::LeanObject,
    mut v_snd_4262_: *mut crate::leanh::LeanObject,
    mut v_minorArgs_4263_: *mut crate::leanh::LeanObject,
    mut v_minorResultType_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
    mut v___y_4266_: *mut crate::leanh::LeanObject,
    mut v___y_4267_: *mut crate::leanh::LeanObject,
    mut v___y_4268_: *mut crate::leanh::LeanObject,
    mut v___y_4269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4270_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0(v_motive_4260_, v_fst_4261_, v_snd_4262_, v_minorArgs_4263_, v_minorResultType_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
    crate::leanh::lean_dec(v___y_4268_);
    crate::leanh::lean_dec_ref(v___y_4267_);
    crate::leanh::lean_dec(v___y_4266_);
    crate::leanh::lean_dec_ref(v___y_4265_);
    crate::leanh::lean_dec_ref(v_minorArgs_4263_);
    crate::leanh::lean_dec(v_snd_4262_);
    return v_res_4270_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(
    mut v_upperBound_4271_: *mut crate::leanh::LeanObject,
    mut v_motive_4272_: *mut crate::leanh::LeanObject,
    mut v_xs_4273_: *mut crate::leanh::LeanObject,
    mut v_numParams_4274_: *mut crate::leanh::LeanObject,
    mut v_majorPos_4275_: *mut crate::leanh::LeanObject,
    mut v_numIndices_4276_: *mut crate::leanh::LeanObject,
    mut v_a_4277_: *mut crate::leanh::LeanObject,
    mut v_b_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
    mut v___y_4280_: *mut crate::leanh::LeanObject,
    mut v___y_4281_: *mut crate::leanh::LeanObject,
    mut v___y_4282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: u8 = 0;
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursor_4298_: u8 = 0;
    let mut v___f_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4309_: u8 = 0;
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4313_: u8 = 0;
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: u8 = 0;
    let mut v___x_4316_: u8 = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4289_ = lean_nat_dec_lt(v_a_4277_, v_upperBound_4271_);
                if v___x_4289_ == 0 {
                    crate::leanh::lean_dec(v_a_4277_);
                    crate::leanh::lean_dec_ref(v_motive_4272_);
                    v___x_4290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4290_, 0, v_b_4278_);
                    return v___x_4290_;
                } else {
                    v_fst_4291_ = crate::leanh::lean_ctor_get(v_b_4278_, 0);
                    v_snd_4292_ = crate::leanh::lean_ctor_get(v_b_4278_, 1);
                    v_isSharedCheck_4323_ = (!crate::leanh::lean_is_exclusive(v_b_4278_)) as u8;
                    if v_isSharedCheck_4323_ == 0 {
                        v___x_4294_ = v_b_4278_;
                        v_isShared_4295_ = v_isSharedCheck_4323_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4292_);
                        crate::leanh::lean_inc(v_fst_4291_);
                        crate::leanh::lean_dec(v_b_4278_);
                        v___x_4294_ = crate::leanh::lean_box(0);
                        v_isShared_4295_ = v_isSharedCheck_4323_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4286_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4287_ = lean_nat_add(v_a_4277_, v___x_4286_);
                crate::leanh::lean_dec(v_a_4277_);
                v_a_4277_ = v___x_4287_;
                v_b_4278_ = v_a_4285_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4296_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4297_ = lean_nat_add(v_numParams_4274_, v___x_4296_);
                v_recursor_4298_ = lean_nat_dec_lt(v_a_4277_, v___x_4297_);
                crate::leanh::lean_dec(v___x_4297_);
                if v_recursor_4298_ == 0 {
                    crate::leanh::lean_inc(v_snd_4292_);
                    crate::leanh::lean_inc(v_fst_4291_);
                    crate::leanh::lean_inc_ref(v_motive_4272_);
                    v___f_4299_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                    crate::leanh::lean_closure_set(v___f_4299_, 0, v_motive_4272_);
                    crate::leanh::lean_closure_set(v___f_4299_, 1, v_fst_4291_);
                    crate::leanh::lean_closure_set(v___f_4299_, 2, v_snd_4292_);
                    v___x_4314_ = lean_nat_sub(v_majorPos_4275_, v_numIndices_4276_);
                    v___x_4315_ = lean_nat_dec_le(v___x_4314_, v_a_4277_);
                    crate::leanh::lean_dec(v___x_4314_);
                    if v___x_4315_ == 0 {
                        crate::leanh::lean_del_object(v___x_4294_);
                        crate::leanh::lean_dec(v_snd_4292_);
                        crate::leanh::lean_dec(v_fst_4291_);
                        state = 3;
                        continue;
                    } else {
                        v___x_4316_ = lean_nat_dec_le(v_a_4277_, v_majorPos_4275_);
                        if v___x_4316_ == 0 {
                            crate::leanh::lean_del_object(v___x_4294_);
                            crate::leanh::lean_dec(v_snd_4292_);
                            crate::leanh::lean_dec(v_fst_4291_);
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___f_4299_);
                            if v_isShared_4295_ == 0 {
                                v___x_4318_ = v___x_4294_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_4319_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_fst_4291_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_snd_4292_);
                                v___x_4318_ = v_reuseFailAlloc_4319_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    if v_isShared_4295_ == 0 {
                        v___x_4321_ = v___x_4294_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_fst_4291_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_snd_4292_);
                        v___x_4321_ = v_reuseFailAlloc_4322_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4301_ = lean_array_fget_borrowed(v_xs_4273_, v_a_4277_);
                crate::leanh::lean_inc(v___y_4282_);
                crate::leanh::lean_inc_ref(v___y_4281_);
                crate::leanh::lean_inc(v___y_4280_);
                crate::leanh::lean_inc_ref(v___y_4279_);
                crate::leanh::lean_inc(v___x_4301_);
                v___x_4302_ = lean_infer_type(
                    v___x_4301_,
                    v___y_4279_,
                    v___y_4280_,
                    v___y_4281_,
                    v___y_4282_,
                );
                if crate::leanh::lean_obj_tag(v___x_4302_) == 0 {
                    v_a_4303_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                    crate::leanh::lean_inc(v_a_4303_);
                    crate::leanh::lean_dec_ref_known(v___x_4302_, 1);
                    v___x_4304_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_a_4303_, v___f_4299_, v_recursor_4298_, v_recursor_4298_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
                    if crate::leanh::lean_obj_tag(v___x_4304_) == 0 {
                        v_a_4305_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                        crate::leanh::lean_inc(v_a_4305_);
                        crate::leanh::lean_dec_ref_known(v___x_4304_, 1);
                        v_a_4285_ = v_a_4305_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_4277_);
                        crate::leanh::lean_dec_ref(v_motive_4272_);
                        return v___x_4304_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_4299_);
                    crate::leanh::lean_dec(v_a_4277_);
                    crate::leanh::lean_dec_ref(v_motive_4272_);
                    v_a_4306_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                    v_isSharedCheck_4313_ = (!crate::leanh::lean_is_exclusive(v___x_4302_)) as u8;
                    if v_isSharedCheck_4313_ == 0 {
                        v___x_4308_ = v___x_4302_;
                        v_isShared_4309_ = v_isSharedCheck_4313_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4306_);
                        crate::leanh::lean_dec(v___x_4302_);
                        v___x_4308_ = crate::leanh::lean_box(0);
                        v_isShared_4309_ = v_isSharedCheck_4313_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4309_ == 0 {
                    v___x_4311_ = v___x_4308_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4312_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
                    v___x_4311_ = v_reuseFailAlloc_4312_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4311_;
            }
            6 => {
                v_a_4285_ = v___x_4318_;
                state = 1;
                continue;
            }
            7 => {
                v_a_4285_ = v___x_4321_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___boxed(
    mut v_upperBound_4324_: *mut crate::leanh::LeanObject,
    mut v_motive_4325_: *mut crate::leanh::LeanObject,
    mut v_xs_4326_: *mut crate::leanh::LeanObject,
    mut v_numParams_4327_: *mut crate::leanh::LeanObject,
    mut v_majorPos_4328_: *mut crate::leanh::LeanObject,
    mut v_numIndices_4329_: *mut crate::leanh::LeanObject,
    mut v_a_4330_: *mut crate::leanh::LeanObject,
    mut v_b_4331_: *mut crate::leanh::LeanObject,
    mut v___y_4332_: *mut crate::leanh::LeanObject,
    mut v___y_4333_: *mut crate::leanh::LeanObject,
    mut v___y_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4337_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v_upperBound_4324_, v_motive_4325_, v_xs_4326_, v_numParams_4327_, v_majorPos_4328_, v_numIndices_4329_, v_a_4330_, v_b_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
    crate::leanh::lean_dec(v___y_4335_);
    crate::leanh::lean_dec_ref(v___y_4334_);
    crate::leanh::lean_dec(v___y_4333_);
    crate::leanh::lean_dec_ref(v___y_4332_);
    crate::leanh::lean_dec(v_numIndices_4329_);
    crate::leanh::lean_dec(v_majorPos_4328_);
    crate::leanh::lean_dec(v_numParams_4327_);
    crate::leanh::lean_dec_ref(v_xs_4326_);
    crate::leanh::lean_dec(v_upperBound_4324_);
    return v_res_4337_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(
    mut v_xs_4344_: *mut crate::leanh::LeanObject,
    mut v_numParams_4345_: *mut crate::leanh::LeanObject,
    mut v_numIndices_4346_: *mut crate::leanh::LeanObject,
    mut v_majorPos_4347_: *mut crate::leanh::LeanObject,
    mut v_motive_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_a_4350_: *mut crate::leanh::LeanObject,
    mut v_a_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4361_: u8 = 0;
    let mut v_fst_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4374_: u8 = 0;
    let mut v_isSharedCheck_4375_: u8 = 0;
    let mut v_a_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4379_: u8 = 0;
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4354_ = lean_array_get_size(v_xs_4344_);
                v___x_4355_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4356_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1;
                v___x_4357_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v___x_4354_, v_motive_4348_, v_xs_4344_, v_numParams_4345_, v_majorPos_4347_, v_numIndices_4346_, v___x_4355_, v___x_4356_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_);
                if crate::leanh::lean_obj_tag(v___x_4357_) == 0 {
                    v_a_4358_ = crate::leanh::lean_ctor_get(v___x_4357_, 0);
                    v_isSharedCheck_4375_ = (!crate::leanh::lean_is_exclusive(v___x_4357_)) as u8;
                    if v_isSharedCheck_4375_ == 0 {
                        v___x_4360_ = v___x_4357_;
                        v_isShared_4361_ = v_isSharedCheck_4375_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4358_);
                        crate::leanh::lean_dec(v___x_4357_);
                        v___x_4360_ = crate::leanh::lean_box(0);
                        v_isShared_4361_ = v_isSharedCheck_4375_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4376_ = crate::leanh::lean_ctor_get(v___x_4357_, 0);
                    v_isSharedCheck_4383_ = (!crate::leanh::lean_is_exclusive(v___x_4357_)) as u8;
                    if v_isSharedCheck_4383_ == 0 {
                        v___x_4378_ = v___x_4357_;
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4376_);
                        crate::leanh::lean_dec(v___x_4357_);
                        v___x_4378_ = crate::leanh::lean_box(0);
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4362_ = crate::leanh::lean_ctor_get(v_a_4358_, 0);
                v_snd_4363_ = crate::leanh::lean_ctor_get(v_a_4358_, 1);
                v_isSharedCheck_4374_ = (!crate::leanh::lean_is_exclusive(v_a_4358_)) as u8;
                if v_isSharedCheck_4374_ == 0 {
                    v___x_4365_ = v_a_4358_;
                    v_isShared_4366_ = v_isSharedCheck_4374_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4363_);
                    crate::leanh::lean_inc(v_fst_4362_);
                    crate::leanh::lean_dec(v_a_4358_);
                    v___x_4365_ = crate::leanh::lean_box(0);
                    v_isShared_4366_ = v_isSharedCheck_4374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4367_ = lean_array_to_list(v_fst_4362_);
                if v_isShared_4366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4365_, 0, v___x_4367_);
                    v___x_4369_ = v___x_4365_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4373_, 1, v_snd_4363_);
                    v___x_4369_ = v_reuseFailAlloc_4373_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4361_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4360_, 0, v___x_4369_);
                    v___x_4371_ = v___x_4360_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4372_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4369_);
                    v___x_4371_ = v_reuseFailAlloc_4372_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4371_;
            }
            5 => {
                if v_isShared_4379_ == 0 {
                    v___x_4381_ = v___x_4378_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
                    v___x_4381_ = v_reuseFailAlloc_4382_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___boxed(
    mut v_xs_4384_: *mut crate::leanh::LeanObject,
    mut v_numParams_4385_: *mut crate::leanh::LeanObject,
    mut v_numIndices_4386_: *mut crate::leanh::LeanObject,
    mut v_majorPos_4387_: *mut crate::leanh::LeanObject,
    mut v_motive_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
    mut v_a_4390_: *mut crate::leanh::LeanObject,
    mut v_a_4391_: *mut crate::leanh::LeanObject,
    mut v_a_4392_: *mut crate::leanh::LeanObject,
    mut v_a_4393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4394_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(
        v_xs_4384_,
        v_numParams_4385_,
        v_numIndices_4386_,
        v_majorPos_4387_,
        v_motive_4388_,
        v_a_4389_,
        v_a_4390_,
        v_a_4391_,
        v_a_4392_,
    );
    crate::leanh::lean_dec(v_a_4392_);
    crate::leanh::lean_dec_ref(v_a_4391_);
    crate::leanh::lean_dec(v_a_4390_);
    crate::leanh::lean_dec_ref(v_a_4389_);
    crate::leanh::lean_dec(v_majorPos_4387_);
    crate::leanh::lean_dec(v_numIndices_4386_);
    crate::leanh::lean_dec(v_numParams_4385_);
    crate::leanh::lean_dec_ref(v_xs_4384_);
    return v_res_4394_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(
    mut v_upperBound_4395_: *mut crate::leanh::LeanObject,
    mut v_motive_4396_: *mut crate::leanh::LeanObject,
    mut v_xs_4397_: *mut crate::leanh::LeanObject,
    mut v_numParams_4398_: *mut crate::leanh::LeanObject,
    mut v_majorPos_4399_: *mut crate::leanh::LeanObject,
    mut v_numIndices_4400_: *mut crate::leanh::LeanObject,
    mut v_inst_4401_: *mut crate::leanh::LeanObject,
    mut v_R_4402_: *mut crate::leanh::LeanObject,
    mut v_a_4403_: *mut crate::leanh::LeanObject,
    mut v_b_4404_: *mut crate::leanh::LeanObject,
    mut v_c_4405_: *mut crate::leanh::LeanObject,
    mut v___y_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
    mut v___y_4408_: *mut crate::leanh::LeanObject,
    mut v___y_4409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4411_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg(v_upperBound_4395_, v_motive_4396_, v_xs_4397_, v_numParams_4398_, v_majorPos_4399_, v_numIndices_4400_, v_a_4403_, v_b_4404_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
    return v___x_4411_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___boxed(
    mut v_upperBound_4412_: *mut crate::leanh::LeanObject,
    mut v_motive_4413_: *mut crate::leanh::LeanObject,
    mut v_xs_4414_: *mut crate::leanh::LeanObject,
    mut v_numParams_4415_: *mut crate::leanh::LeanObject,
    mut v_majorPos_4416_: *mut crate::leanh::LeanObject,
    mut v_numIndices_4417_: *mut crate::leanh::LeanObject,
    mut v_inst_4418_: *mut crate::leanh::LeanObject,
    mut v_R_4419_: *mut crate::leanh::LeanObject,
    mut v_a_4420_: *mut crate::leanh::LeanObject,
    mut v_b_4421_: *mut crate::leanh::LeanObject,
    mut v_c_4422_: *mut crate::leanh::LeanObject,
    mut v___y_4423_: *mut crate::leanh::LeanObject,
    mut v___y_4424_: *mut crate::leanh::LeanObject,
    mut v___y_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4428_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3(v_upperBound_4412_, v_motive_4413_, v_xs_4414_, v_numParams_4415_, v_majorPos_4416_, v_numIndices_4417_, v_inst_4418_, v_R_4419_, v_a_4420_, v_b_4421_, v_c_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
    crate::leanh::lean_dec(v___y_4426_);
    crate::leanh::lean_dec_ref(v___y_4425_);
    crate::leanh::lean_dec(v___y_4424_);
    crate::leanh::lean_dec_ref(v___y_4423_);
    crate::leanh::lean_dec(v_numIndices_4417_);
    crate::leanh::lean_dec(v_majorPos_4416_);
    crate::leanh::lean_dec(v_numParams_4415_);
    crate::leanh::lean_dec_ref(v_xs_4414_);
    crate::leanh::lean_dec(v_upperBound_4412_);
    return v_res_4428_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4430_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__0;
    v___x_4431_ = l_Lean_stringToMessageData(v___x_4430_);
    return v___x_4431_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(
    mut v_declName_4432_: *mut crate::leanh::LeanObject,
    mut v_motiveArgs_4433_: *mut crate::leanh::LeanObject,
    mut v_motiveResultType_4434_: *mut crate::leanh::LeanObject,
    mut v_motiveTypeParams_4435_: *mut crate::leanh::LeanObject,
    mut v_a_4436_: *mut crate::leanh::LeanObject,
    mut v_a_4437_: *mut crate::leanh::LeanObject,
    mut v_a_4438_: *mut crate::leanh::LeanObject,
    mut v_a_4439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: u8 = 0;
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: u8 = 0;
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: u8 = 0;
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4449_ = l_Lean_Expr_isSort(v_motiveResultType_4434_);
                if v___x_4449_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_4450_ = lean_array_get_size(v_motiveArgs_4433_);
                    v___x_4451_ = lean_array_get_size(v_motiveTypeParams_4435_);
                    v___x_4452_ = lean_nat_dec_eq(v___x_4450_, v___x_4451_);
                    if v___x_4452_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_4432_);
                        v___x_4453_ = crate::leanh::lean_box(0);
                        v___x_4454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4454_, 0, v___x_4453_);
                        return v___x_4454_;
                    }
                }
            }
            1 => {
                v___x_4442_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
                v___x_4443_ = 0;
                v___x_4444_ = l_Lean_MessageData_ofConstName(v_declName_4432_, v___x_4443_);
                v___x_4445_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4445_, 0, v___x_4442_);
                crate::leanh::lean_ctor_set(v___x_4445_, 1, v___x_4444_);
                v___x_4446_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1);
                v___x_4447_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4447_, 0, v___x_4445_);
                crate::leanh::lean_ctor_set(v___x_4447_, 1, v___x_4446_);
                v___x_4448_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_4447_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_);
                return v___x_4448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___boxed(
    mut v_declName_4455_: *mut crate::leanh::LeanObject,
    mut v_motiveArgs_4456_: *mut crate::leanh::LeanObject,
    mut v_motiveResultType_4457_: *mut crate::leanh::LeanObject,
    mut v_motiveTypeParams_4458_: *mut crate::leanh::LeanObject,
    mut v_a_4459_: *mut crate::leanh::LeanObject,
    mut v_a_4460_: *mut crate::leanh::LeanObject,
    mut v_a_4461_: *mut crate::leanh::LeanObject,
    mut v_a_4462_: *mut crate::leanh::LeanObject,
    mut v_a_4463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4464_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(
        v_declName_4455_,
        v_motiveArgs_4456_,
        v_motiveResultType_4457_,
        v_motiveTypeParams_4458_,
        v_a_4459_,
        v_a_4460_,
        v_a_4461_,
        v_a_4462_,
    );
    crate::leanh::lean_dec(v_a_4462_);
    crate::leanh::lean_dec_ref(v_a_4461_);
    crate::leanh::lean_dec(v_a_4460_);
    crate::leanh::lean_dec_ref(v_a_4459_);
    crate::leanh::lean_dec_ref(v_motiveTypeParams_4458_);
    crate::leanh::lean_dec_ref(v_motiveResultType_4457_);
    crate::leanh::lean_dec_ref(v_motiveArgs_4456_);
    return v_res_4464_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(
    mut v_declName_4465_: *mut crate::leanh::LeanObject,
    mut v_motiveArgs_4466_: *mut crate::leanh::LeanObject,
    mut v_a_4467_: *mut crate::leanh::LeanObject,
    mut v_us_4468_: *mut crate::leanh::LeanObject,
    mut v_xs_4469_: *mut crate::leanh::LeanObject,
    mut v___x_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
    mut v_fst_4472_: *mut crate::leanh::LeanObject,
    mut v_motive_4473_: *mut crate::leanh::LeanObject,
    mut v_declName_4474_: *mut crate::leanh::LeanObject,
    mut v_snd_4475_: u8,
    mut v_a_4476_: *mut crate::leanh::LeanObject,
    mut v_a_4477_: *mut crate::leanh::LeanObject,
    mut v_motiveTypeParams_4478_: *mut crate::leanh::LeanObject,
    mut v_motiveResultType_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
    mut v___y_4483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4495_: u8 = 0;
    let mut v_fst_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut v_a_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4508_: u8 = 0;
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4512_: u8 = 0;
    let mut v_a_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4516_: u8 = 0;
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4520_: u8 = 0;
    let mut v_a_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut v_a_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4532_: u8 = 0;
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_4465_);
                v___x_4485_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(
                    v_declName_4465_,
                    v_motiveArgs_4466_,
                    v_motiveResultType_4479_,
                    v_motiveTypeParams_4478_,
                    v___y_4480_,
                    v___y_4481_,
                    v___y_4482_,
                    v___y_4483_,
                );
                if crate::leanh::lean_obj_tag(v___x_4485_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4485_, 1);
                    crate::leanh::lean_inc(v_declName_4465_);
                    v___x_4486_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(
                        v_declName_4465_,
                        v_motiveResultType_4479_,
                        v___y_4480_,
                        v___y_4481_,
                        v___y_4482_,
                        v___y_4483_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4486_) == 0 {
                        v_a_4487_ = crate::leanh::lean_ctor_get(v___x_4486_, 0);
                        crate::leanh::lean_inc(v_a_4487_);
                        crate::leanh::lean_dec_ref_known(v___x_4486_, 1);
                        v___x_4488_ = l_Lean_ConstantInfo_levelParams(v_a_4467_);
                        crate::leanh::lean_inc(v_declName_4465_);
                        v___x_4489_ =
                            l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(
                                v_declName_4465_,
                                v___x_4488_,
                                v_a_4487_,
                                v_us_4468_,
                                v___y_4480_,
                                v___y_4481_,
                                v___y_4482_,
                                v___y_4483_,
                            );
                        crate::leanh::lean_dec(v_a_4487_);
                        crate::leanh::lean_dec(v___x_4488_);
                        if crate::leanh::lean_obj_tag(v___x_4489_) == 0 {
                            v_a_4490_ = crate::leanh::lean_ctor_get(v___x_4489_, 0);
                            crate::leanh::lean_inc(v_a_4490_);
                            crate::leanh::lean_dec_ref_known(v___x_4489_, 1);
                            v___x_4491_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(v_xs_4469_, v___x_4470_, v___y_4471_, v_fst_4472_, v_motive_4473_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
                            if crate::leanh::lean_obj_tag(v___x_4491_) == 0 {
                                v_a_4492_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
                                v_isSharedCheck_4504_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4491_)) as u8;
                                if v_isSharedCheck_4504_ == 0 {
                                    v___x_4494_ = v___x_4491_;
                                    v_isShared_4495_ = v_isSharedCheck_4504_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4492_);
                                    crate::leanh::lean_dec(v___x_4491_);
                                    v___x_4494_ = crate::leanh::lean_box(0);
                                    v_isShared_4495_ = v_isSharedCheck_4504_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4490_);
                                crate::leanh::lean_dec(v_a_4477_);
                                crate::leanh::lean_dec(v_a_4476_);
                                crate::leanh::lean_dec(v_declName_4474_);
                                crate::leanh::lean_dec(v_fst_4472_);
                                crate::leanh::lean_dec(v_declName_4465_);
                                v_a_4505_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
                                v_isSharedCheck_4512_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4491_)) as u8;
                                if v_isSharedCheck_4512_ == 0 {
                                    v___x_4507_ = v___x_4491_;
                                    v_isShared_4508_ = v_isSharedCheck_4512_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4505_);
                                    crate::leanh::lean_dec(v___x_4491_);
                                    v___x_4507_ = crate::leanh::lean_box(0);
                                    v_isShared_4508_ = v_isSharedCheck_4512_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4477_);
                            crate::leanh::lean_dec(v_a_4476_);
                            crate::leanh::lean_dec(v_declName_4474_);
                            crate::leanh::lean_dec_ref(v_motive_4473_);
                            crate::leanh::lean_dec(v_fst_4472_);
                            crate::leanh::lean_dec(v_declName_4465_);
                            v_a_4513_ = crate::leanh::lean_ctor_get(v___x_4489_, 0);
                            v_isSharedCheck_4520_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4489_)) as u8;
                            if v_isSharedCheck_4520_ == 0 {
                                v___x_4515_ = v___x_4489_;
                                v_isShared_4516_ = v_isSharedCheck_4520_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4513_);
                                crate::leanh::lean_dec(v___x_4489_);
                                v___x_4515_ = crate::leanh::lean_box(0);
                                v_isShared_4516_ = v_isSharedCheck_4520_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4477_);
                        crate::leanh::lean_dec(v_a_4476_);
                        crate::leanh::lean_dec(v_declName_4474_);
                        crate::leanh::lean_dec_ref(v_motive_4473_);
                        crate::leanh::lean_dec(v_fst_4472_);
                        crate::leanh::lean_dec(v_us_4468_);
                        crate::leanh::lean_dec(v_declName_4465_);
                        v_a_4521_ = crate::leanh::lean_ctor_get(v___x_4486_, 0);
                        v_isSharedCheck_4528_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4486_)) as u8;
                        if v_isSharedCheck_4528_ == 0 {
                            v___x_4523_ = v___x_4486_;
                            v_isShared_4524_ = v_isSharedCheck_4528_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4521_);
                            crate::leanh::lean_dec(v___x_4486_);
                            v___x_4523_ = crate::leanh::lean_box(0);
                            v_isShared_4524_ = v_isSharedCheck_4528_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4477_);
                    crate::leanh::lean_dec(v_a_4476_);
                    crate::leanh::lean_dec(v_declName_4474_);
                    crate::leanh::lean_dec_ref(v_motive_4473_);
                    crate::leanh::lean_dec(v_fst_4472_);
                    crate::leanh::lean_dec(v_us_4468_);
                    crate::leanh::lean_dec(v_declName_4465_);
                    v_a_4529_ = crate::leanh::lean_ctor_get(v___x_4485_, 0);
                    v_isSharedCheck_4536_ = (!crate::leanh::lean_is_exclusive(v___x_4485_)) as u8;
                    if v_isSharedCheck_4536_ == 0 {
                        v___x_4531_ = v___x_4485_;
                        v_isShared_4532_ = v_isSharedCheck_4536_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4529_);
                        crate::leanh::lean_dec(v___x_4485_);
                        v___x_4531_ = crate::leanh::lean_box(0);
                        v_isShared_4532_ = v_isSharedCheck_4536_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4496_ = crate::leanh::lean_ctor_get(v_a_4492_, 0);
                crate::leanh::lean_inc(v_fst_4496_);
                v_snd_4497_ = crate::leanh::lean_ctor_get(v_a_4492_, 1);
                crate::leanh::lean_inc(v_snd_4497_);
                crate::leanh::lean_dec(v_a_4492_);
                v___x_4498_ = lean_array_get_size(v_xs_4469_);
                v___x_4499_ = crate::leanh::lean_alloc_ctor(0, 8, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4499_, 0, v_declName_4465_);
                crate::leanh::lean_ctor_set(v___x_4499_, 1, v_declName_4474_);
                crate::leanh::lean_ctor_set(v___x_4499_, 2, v_a_4490_);
                crate::leanh::lean_ctor_set(v___x_4499_, 3, v___x_4498_);
                crate::leanh::lean_ctor_set(v___x_4499_, 4, v_fst_4472_);
                crate::leanh::lean_ctor_set(v___x_4499_, 5, v_a_4476_);
                crate::leanh::lean_ctor_set(v___x_4499_, 6, v_a_4477_);
                crate::leanh::lean_ctor_set(v___x_4499_, 7, v_fst_4496_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4499_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    v_snd_4475_,
                );
                v___x_4500_ = (crate::leanh::lean_unbox(v_snd_4497_) as u8);
                crate::leanh::lean_dec(v_snd_4497_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4499_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                    v___x_4500_,
                );
                if v_isShared_4495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4494_, 0, v___x_4499_);
                    v___x_4502_ = v___x_4494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4499_);
                    v___x_4502_ = v_reuseFailAlloc_4503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4502_;
            }
            3 => {
                if v_isShared_4508_ == 0 {
                    v___x_4510_ = v___x_4507_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4511_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
                    v___x_4510_ = v_reuseFailAlloc_4511_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4510_;
            }
            5 => {
                if v_isShared_4516_ == 0 {
                    v___x_4518_ = v___x_4515_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
                    v___x_4518_ = v_reuseFailAlloc_4519_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4518_;
            }
            7 => {
                if v_isShared_4524_ == 0 {
                    v___x_4526_ = v___x_4523_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
                    v___x_4526_ = v_reuseFailAlloc_4527_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4526_;
            }
            9 => {
                if v_isShared_4532_ == 0 {
                    v___x_4534_ = v___x_4531_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4535_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
                    v___x_4534_ = v_reuseFailAlloc_4535_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_4537_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_motiveArgs_4538_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_a_4539_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_us_4540_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_xs_4541_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_4542_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4543_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_fst_4544_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_motive_4545_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_declName_4546_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_snd_4547_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_4548_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_4549_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_motiveTypeParams_4550_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_motiveResultType_4551_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4552_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4553_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4554_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4555_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_4556_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_snd_5191__boxed_4557_: u8 = 0;
    let mut v_res_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_5191__boxed_4557_ = (crate::leanh::lean_unbox(v_snd_4547_) as u8);
    v_res_4558_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0(v_declName_4537_, v_motiveArgs_4538_, v_a_4539_, v_us_4540_, v_xs_4541_, v___x_4542_, v___y_4543_, v_fst_4544_, v_motive_4545_, v_declName_4546_, v_snd_5191__boxed_4557_, v_a_4548_, v_a_4549_, v_motiveTypeParams_4550_, v_motiveResultType_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
    crate::leanh::lean_dec(v___y_4555_);
    crate::leanh::lean_dec_ref(v___y_4554_);
    crate::leanh::lean_dec(v___y_4553_);
    crate::leanh::lean_dec_ref(v___y_4552_);
    crate::leanh::lean_dec_ref(v_motiveResultType_4551_);
    crate::leanh::lean_dec_ref(v_motiveTypeParams_4550_);
    crate::leanh::lean_dec(v___y_4543_);
    crate::leanh::lean_dec(v___x_4542_);
    crate::leanh::lean_dec_ref(v_xs_4541_);
    crate::leanh::lean_dec_ref(v_a_4539_);
    crate::leanh::lean_dec_ref(v_motiveArgs_4538_);
    return v_res_4558_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4560_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__0;
    v___x_4561_ = l_Lean_stringToMessageData(v___x_4560_);
    return v___x_4561_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(
    mut v_declName_4562_: *mut crate::leanh::LeanObject,
    mut v_xs_4563_: *mut crate::leanh::LeanObject,
    mut v___x_4564_: *mut crate::leanh::LeanObject,
    mut v_fst_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
    mut v_motiveArgs_4567_: *mut crate::leanh::LeanObject,
    mut v_a_4568_: *mut crate::leanh::LeanObject,
    mut v_motive_4569_: *mut crate::leanh::LeanObject,
    mut v_snd_4570_: u8,
    mut v_x_4571_: *mut crate::leanh::LeanObject,
    mut v_x_4572_: *mut crate::leanh::LeanObject,
    mut v_x_4573_: *mut crate::leanh::LeanObject,
    mut v___y_4574_: *mut crate::leanh::LeanObject,
    mut v___y_4575_: *mut crate::leanh::LeanObject,
    mut v___y_4576_: *mut crate::leanh::LeanObject,
    mut v___y_4577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: u8 = 0;
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4600_: u8 = 0;
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4604_: u8 = 0;
    let mut v_a_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4612_: u8 = 0;
    let mut v_a_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4616_: u8 = 0;
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4620_: u8 = 0;
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: u8 = 0;
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4571_) == 5 {
                    v_fn_4579_ = crate::leanh::lean_ctor_get(v_x_4571_, 0);
                    crate::leanh::lean_inc_ref(v_fn_4579_);
                    v_arg_4580_ = crate::leanh::lean_ctor_get(v_x_4571_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4580_);
                    crate::leanh::lean_dec_ref_known(v_x_4571_, 2);
                    v___x_4581_ = lean_array_set(v_x_4572_, v_x_4573_, v_arg_4580_);
                    v___x_4582_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4583_ = lean_nat_sub(v_x_4573_, v___x_4582_);
                    crate::leanh::lean_dec(v_x_4573_);
                    v_x_4571_ = v_fn_4579_;
                    v_x_4572_ = v___x_4581_;
                    v_x_4573_ = v___x_4583_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_4573_);
                    if crate::leanh::lean_obj_tag(v_x_4571_) == 4 {
                        v_declName_4585_ = crate::leanh::lean_ctor_get(v_x_4571_, 0);
                        crate::leanh::lean_inc(v_declName_4585_);
                        v_us_4586_ = crate::leanh::lean_ctor_get(v_x_4571_, 1);
                        crate::leanh::lean_inc(v_us_4586_);
                        crate::leanh::lean_dec_ref_known(v_x_4571_, 2);
                        crate::leanh::lean_inc(v_declName_4562_);
                        v___x_4587_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(
                            v_declName_4562_,
                            v_xs_4563_,
                            v___x_4564_,
                            v_x_4572_,
                            v___y_4574_,
                            v___y_4575_,
                            v___y_4576_,
                            v___y_4577_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4587_) == 0 {
                            v_a_4588_ = crate::leanh::lean_ctor_get(v___x_4587_, 0);
                            crate::leanh::lean_inc(v_a_4588_);
                            crate::leanh::lean_dec_ref_known(v___x_4587_, 1);
                            crate::leanh::lean_inc(v_declName_4562_);
                            v___x_4589_ =
                                l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(
                                    v_declName_4562_,
                                    v_xs_4563_,
                                    v_fst_4565_,
                                    v___y_4566_,
                                    v_x_4572_,
                                    v___y_4574_,
                                    v___y_4575_,
                                    v___y_4576_,
                                    v___y_4577_,
                                );
                            crate::leanh::lean_dec_ref(v_x_4572_);
                            if crate::leanh::lean_obj_tag(v___x_4589_) == 0 {
                                v_a_4590_ = crate::leanh::lean_ctor_get(v___x_4589_, 0);
                                crate::leanh::lean_inc(v_a_4590_);
                                crate::leanh::lean_dec_ref_known(v___x_4589_, 1);
                                crate::leanh::lean_inc(v___y_4577_);
                                crate::leanh::lean_inc_ref(v___y_4576_);
                                crate::leanh::lean_inc(v___y_4575_);
                                crate::leanh::lean_inc_ref(v___y_4574_);
                                crate::leanh::lean_inc_ref(v_motive_4569_);
                                v___x_4591_ = lean_infer_type(
                                    v_motive_4569_,
                                    v___y_4574_,
                                    v___y_4575_,
                                    v___y_4576_,
                                    v___y_4577_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4591_) == 0 {
                                    v_a_4592_ = crate::leanh::lean_ctor_get(v___x_4591_, 0);
                                    crate::leanh::lean_inc(v_a_4592_);
                                    crate::leanh::lean_dec_ref_known(v___x_4591_, 1);
                                    v___x_4593_ = crate::leanh::lean_box((v_snd_4570_) as usize);
                                    v___f_4594_ = crate::leanh::lean_alloc_closure(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___lam__0___boxed as *mut core::ffi::c_void, 20, 13);
                                    crate::leanh::lean_closure_set(
                                        v___f_4594_,
                                        0,
                                        v_declName_4562_,
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___f_4594_,
                                        1,
                                        v_motiveArgs_4567_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_4594_, 2, v_a_4568_);
                                    crate::leanh::lean_closure_set(v___f_4594_, 3, v_us_4586_);
                                    crate::leanh::lean_closure_set(v___f_4594_, 4, v_xs_4563_);
                                    crate::leanh::lean_closure_set(v___f_4594_, 5, v___x_4564_);
                                    crate::leanh::lean_closure_set(v___f_4594_, 6, v___y_4566_);
                                    crate::leanh::lean_closure_set(v___f_4594_, 7, v_fst_4565_);
                                    crate::leanh::lean_closure_set(v___f_4594_, 8, v_motive_4569_);
                                    crate::leanh::lean_closure_set(
                                        v___f_4594_,
                                        9,
                                        v_declName_4585_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_4594_, 10, v___x_4593_);
                                    crate::leanh::lean_closure_set(v___f_4594_, 11, v_a_4588_);
                                    crate::leanh::lean_closure_set(v___f_4594_, 12, v_a_4590_);
                                    v___x_4595_ = 0;
                                    v___x_4596_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v_a_4592_, v___f_4594_, v___x_4595_, v___x_4595_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
                                    return v___x_4596_;
                                } else {
                                    crate::leanh::lean_dec(v_a_4590_);
                                    crate::leanh::lean_dec(v_a_4588_);
                                    crate::leanh::lean_dec(v_us_4586_);
                                    crate::leanh::lean_dec(v_declName_4585_);
                                    crate::leanh::lean_dec_ref(v_motive_4569_);
                                    crate::leanh::lean_dec_ref(v_a_4568_);
                                    crate::leanh::lean_dec_ref(v_motiveArgs_4567_);
                                    crate::leanh::lean_dec(v___y_4566_);
                                    crate::leanh::lean_dec(v_fst_4565_);
                                    crate::leanh::lean_dec(v___x_4564_);
                                    crate::leanh::lean_dec_ref(v_xs_4563_);
                                    crate::leanh::lean_dec(v_declName_4562_);
                                    v_a_4597_ = crate::leanh::lean_ctor_get(v___x_4591_, 0);
                                    v_isSharedCheck_4604_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4591_)) as u8;
                                    if v_isSharedCheck_4604_ == 0 {
                                        v___x_4599_ = v___x_4591_;
                                        v_isShared_4600_ = v_isSharedCheck_4604_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4597_);
                                        crate::leanh::lean_dec(v___x_4591_);
                                        v___x_4599_ = crate::leanh::lean_box(0);
                                        v_isShared_4600_ = v_isSharedCheck_4604_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4588_);
                                crate::leanh::lean_dec(v_us_4586_);
                                crate::leanh::lean_dec(v_declName_4585_);
                                crate::leanh::lean_dec_ref(v_motive_4569_);
                                crate::leanh::lean_dec_ref(v_a_4568_);
                                crate::leanh::lean_dec_ref(v_motiveArgs_4567_);
                                crate::leanh::lean_dec(v___y_4566_);
                                crate::leanh::lean_dec(v_fst_4565_);
                                crate::leanh::lean_dec(v___x_4564_);
                                crate::leanh::lean_dec_ref(v_xs_4563_);
                                crate::leanh::lean_dec(v_declName_4562_);
                                v_a_4605_ = crate::leanh::lean_ctor_get(v___x_4589_, 0);
                                v_isSharedCheck_4612_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4589_)) as u8;
                                if v_isSharedCheck_4612_ == 0 {
                                    v___x_4607_ = v___x_4589_;
                                    v_isShared_4608_ = v_isSharedCheck_4612_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4605_);
                                    crate::leanh::lean_dec(v___x_4589_);
                                    v___x_4607_ = crate::leanh::lean_box(0);
                                    v_isShared_4608_ = v_isSharedCheck_4612_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_us_4586_);
                            crate::leanh::lean_dec(v_declName_4585_);
                            crate::leanh::lean_dec_ref(v_x_4572_);
                            crate::leanh::lean_dec_ref(v_motive_4569_);
                            crate::leanh::lean_dec_ref(v_a_4568_);
                            crate::leanh::lean_dec_ref(v_motiveArgs_4567_);
                            crate::leanh::lean_dec(v___y_4566_);
                            crate::leanh::lean_dec(v_fst_4565_);
                            crate::leanh::lean_dec(v___x_4564_);
                            crate::leanh::lean_dec_ref(v_xs_4563_);
                            crate::leanh::lean_dec(v_declName_4562_);
                            v_a_4613_ = crate::leanh::lean_ctor_get(v___x_4587_, 0);
                            v_isSharedCheck_4620_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4587_)) as u8;
                            if v_isSharedCheck_4620_ == 0 {
                                v___x_4615_ = v___x_4587_;
                                v_isShared_4616_ = v_isSharedCheck_4620_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4613_);
                                crate::leanh::lean_dec(v___x_4587_);
                                v___x_4615_ = crate::leanh::lean_box(0);
                                v_isShared_4616_ = v_isSharedCheck_4620_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_4572_);
                        crate::leanh::lean_dec_ref(v_x_4571_);
                        crate::leanh::lean_dec_ref(v_motive_4569_);
                        crate::leanh::lean_dec_ref(v_a_4568_);
                        crate::leanh::lean_dec_ref(v_motiveArgs_4567_);
                        crate::leanh::lean_dec(v___y_4566_);
                        crate::leanh::lean_dec(v_fst_4565_);
                        crate::leanh::lean_dec(v___x_4564_);
                        crate::leanh::lean_dec_ref(v_xs_4563_);
                        v___x_4621_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
                        v___x_4622_ = 0;
                        v___x_4623_ = l_Lean_MessageData_ofConstName(v_declName_4562_, v___x_4622_);
                        v___x_4624_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4624_, 0, v___x_4621_);
                        crate::leanh::lean_ctor_set(v___x_4624_, 1, v___x_4623_);
                        v___x_4625_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___closed__1);
                        v___x_4626_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4626_, 0, v___x_4624_);
                        crate::leanh::lean_ctor_set(v___x_4626_, 1, v___x_4625_);
                        v___x_4627_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_4626_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
                        return v___x_4627_;
                    }
                }
            }
            1 => {
                if v_isShared_4600_ == 0 {
                    v___x_4602_ = v___x_4599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
                    v___x_4602_ = v_reuseFailAlloc_4603_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4602_;
            }
            3 => {
                if v_isShared_4608_ == 0 {
                    v___x_4610_ = v___x_4607_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
                    v___x_4610_ = v_reuseFailAlloc_4611_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4610_;
            }
            5 => {
                if v_isShared_4616_ == 0 {
                    v___x_4618_ = v___x_4615_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
                    v___x_4618_ = v_reuseFailAlloc_4619_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_4628_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_xs_4629_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4630_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_fst_4631_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___y_4632_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_motiveArgs_4633_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_4634_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_motive_4635_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_snd_4636_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_x_4637_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_x_4638_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_x_4639_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4640_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4641_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4642_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4643_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4644_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_snd_5345__boxed_4645_: u8 = 0;
    let mut v_res_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_5345__boxed_4645_ = (crate::leanh::lean_unbox(v_snd_4636_) as u8);
    v_res_4646_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(v_declName_4628_, v_xs_4629_, v___x_4630_, v_fst_4631_, v___y_4632_, v_motiveArgs_4633_, v_a_4634_, v_motive_4635_, v_snd_5345__boxed_4645_, v_x_4637_, v_x_4638_, v_x_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
    crate::leanh::lean_dec(v___y_4643_);
    crate::leanh::lean_dec_ref(v___y_4642_);
    crate::leanh::lean_dec(v___y_4641_);
    crate::leanh::lean_dec_ref(v___y_4640_);
    return v_res_4646_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4648_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__0;
    v___x_4649_ = l_Lean_stringToMessageData(v___x_4648_);
    return v___x_4649_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(
    mut v_declName_4650_: *mut crate::leanh::LeanObject,
    mut v_a_4651_: *mut crate::leanh::LeanObject,
    mut v_xs_4652_: *mut crate::leanh::LeanObject,
    mut v_a_4653_: *mut crate::leanh::LeanObject,
    mut v_x_4654_: *mut crate::leanh::LeanObject,
    mut v_x_4655_: *mut crate::leanh::LeanObject,
    mut v_x_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v_fst_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4680_: u8 = 0;
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: u8 = 0;
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4701_: u8 = 0;
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4705_: u8 = 0;
    let mut v___y_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: u8 = 0;
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: u8 = 0;
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4721_: u8 = 0;
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut v_reuseFailAlloc_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: u8 = 0;
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4733_: u8 = 0;
    let mut v_isSharedCheck_4734_: u8 = 0;
    let mut v_a_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4738_: u8 = 0;
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4742_: u8 = 0;
    let mut v_a_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4746_: u8 = 0;
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4654_) == 5 {
                    v_fn_4662_ = crate::leanh::lean_ctor_get(v_x_4654_, 0);
                    crate::leanh::lean_inc_ref(v_fn_4662_);
                    v_arg_4663_ = crate::leanh::lean_ctor_get(v_x_4654_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4663_);
                    crate::leanh::lean_dec_ref_known(v_x_4654_, 2);
                    v___x_4664_ = lean_array_set(v_x_4655_, v_x_4656_, v_arg_4663_);
                    v___x_4665_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4666_ = lean_nat_sub(v_x_4656_, v___x_4665_);
                    crate::leanh::lean_dec(v_x_4656_);
                    v_x_4654_ = v_fn_4662_;
                    v_x_4655_ = v___x_4664_;
                    v_x_4656_ = v___x_4666_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_4656_);
                    crate::leanh::lean_inc(v_declName_4650_);
                    v___x_4668_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(
                        v_declName_4650_,
                        v_x_4654_,
                        v_x_4655_,
                        v___y_4657_,
                        v___y_4658_,
                        v___y_4659_,
                        v___y_4660_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4668_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4668_, 1);
                        crate::leanh::lean_inc(v_declName_4650_);
                        v___x_4669_ =
                            l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(
                                v_declName_4650_,
                                v_a_4651_,
                                v_xs_4652_,
                                v_x_4655_,
                                v___y_4657_,
                                v___y_4658_,
                                v___y_4659_,
                                v___y_4660_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_4669_) == 0 {
                            v_a_4670_ = crate::leanh::lean_ctor_get(v___x_4669_, 0);
                            crate::leanh::lean_inc(v_a_4670_);
                            crate::leanh::lean_dec_ref_known(v___x_4669_, 1);
                            v_snd_4671_ = crate::leanh::lean_ctor_get(v_a_4670_, 1);
                            v_fst_4672_ = crate::leanh::lean_ctor_get(v_a_4670_, 0);
                            v_isSharedCheck_4734_ =
                                (!crate::leanh::lean_is_exclusive(v_a_4670_)) as u8;
                            if v_isSharedCheck_4734_ == 0 {
                                v___x_4674_ = v_a_4670_;
                                v_isShared_4675_ = v_isSharedCheck_4734_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_4671_);
                                crate::leanh::lean_inc(v_fst_4672_);
                                crate::leanh::lean_dec(v_a_4670_);
                                v___x_4674_ = crate::leanh::lean_box(0);
                                v_isShared_4675_ = v_isSharedCheck_4734_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_x_4655_);
                            crate::leanh::lean_dec_ref(v_x_4654_);
                            crate::leanh::lean_dec_ref(v_a_4653_);
                            crate::leanh::lean_dec_ref(v_xs_4652_);
                            crate::leanh::lean_dec(v_declName_4650_);
                            v_a_4735_ = crate::leanh::lean_ctor_get(v___x_4669_, 0);
                            v_isSharedCheck_4742_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4669_)) as u8;
                            if v_isSharedCheck_4742_ == 0 {
                                v___x_4737_ = v___x_4669_;
                                v_isShared_4738_ = v_isSharedCheck_4742_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4735_);
                                crate::leanh::lean_dec(v___x_4669_);
                                v___x_4737_ = crate::leanh::lean_box(0);
                                v_isShared_4738_ = v_isSharedCheck_4742_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_4655_);
                        crate::leanh::lean_dec_ref(v_x_4654_);
                        crate::leanh::lean_dec_ref(v_a_4653_);
                        crate::leanh::lean_dec_ref(v_xs_4652_);
                        crate::leanh::lean_dec(v_a_4651_);
                        crate::leanh::lean_dec(v_declName_4650_);
                        v_a_4743_ = crate::leanh::lean_ctor_get(v___x_4668_, 0);
                        v_isSharedCheck_4750_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4668_)) as u8;
                        if v_isSharedCheck_4750_ == 0 {
                            v___x_4745_ = v___x_4668_;
                            v_isShared_4746_ = v_isSharedCheck_4750_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4743_);
                            crate::leanh::lean_dec(v___x_4668_);
                            v___x_4745_ = crate::leanh::lean_box(0);
                            v_isShared_4746_ = v_isSharedCheck_4750_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4676_ = crate::leanh::lean_ctor_get(v_snd_4671_, 0);
                v_snd_4677_ = crate::leanh::lean_ctor_get(v_snd_4671_, 1);
                v_isSharedCheck_4733_ = (!crate::leanh::lean_is_exclusive(v_snd_4671_)) as u8;
                if v_isSharedCheck_4733_ == 0 {
                    v___x_4679_ = v_snd_4671_;
                    v_isShared_4680_ = v_isSharedCheck_4733_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4677_);
                    crate::leanh::lean_inc(v_fst_4676_);
                    crate::leanh::lean_dec(v_snd_4671_);
                    v___x_4679_ = crate::leanh::lean_box(0);
                    v_isShared_4680_ = v_isSharedCheck_4733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4681_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4682_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(
                    v_xs_4652_,
                    v_x_4654_,
                    v___x_4681_,
                );
                v___x_4728_ = (crate::leanh::lean_unbox(v_snd_4677_) as u8);
                if v___x_4728_ == 0 {
                    v___x_4729_ = lean_array_get_size(v_x_4655_);
                    v___y_4707_ = v___x_4729_;
                    state = 6;
                    continue;
                } else {
                    v___x_4730_ = lean_array_get_size(v_x_4655_);
                    v___x_4731_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4732_ = lean_nat_sub(v___x_4730_, v___x_4731_);
                    v___y_4707_ = v___x_4732_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v___y_4688_);
                crate::leanh::lean_inc_ref(v___y_4687_);
                crate::leanh::lean_inc(v___y_4686_);
                crate::leanh::lean_inc_ref(v___y_4685_);
                v___x_4689_ = lean_infer_type(
                    v_fst_4672_,
                    v___y_4685_,
                    v___y_4686_,
                    v___y_4687_,
                    v___y_4688_,
                );
                if crate::leanh::lean_obj_tag(v___x_4689_) == 0 {
                    v_a_4690_ = crate::leanh::lean_ctor_get(v___x_4689_, 0);
                    crate::leanh::lean_inc(v_a_4690_);
                    crate::leanh::lean_dec_ref_known(v___x_4689_, 1);
                    v_dummy_4691_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
                    v_nargs_4692_ = l_Lean_Expr_getAppNumArgs(v_a_4690_);
                    crate::leanh::lean_inc(v_nargs_4692_);
                    v___x_4693_ = lean_mk_array(v_nargs_4692_, v_dummy_4691_);
                    v___x_4694_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4695_ = lean_nat_sub(v_nargs_4692_, v___x_4694_);
                    crate::leanh::lean_dec(v_nargs_4692_);
                    v___x_4696_ = (crate::leanh::lean_unbox(v_snd_4677_) as u8);
                    crate::leanh::lean_dec(v_snd_4677_);
                    v___x_4697_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__1(v_declName_4650_, v_xs_4652_, v___x_4682_, v_fst_4676_, v___y_4684_, v_x_4655_, v_a_4653_, v_x_4654_, v___x_4696_, v_a_4690_, v___x_4693_, v___x_4695_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
                    return v___x_4697_;
                } else {
                    crate::leanh::lean_dec(v___y_4684_);
                    crate::leanh::lean_dec(v___x_4682_);
                    crate::leanh::lean_dec(v_snd_4677_);
                    crate::leanh::lean_dec(v_fst_4676_);
                    crate::leanh::lean_dec_ref(v_x_4655_);
                    crate::leanh::lean_dec_ref(v_x_4654_);
                    crate::leanh::lean_dec_ref(v_a_4653_);
                    crate::leanh::lean_dec_ref(v_xs_4652_);
                    crate::leanh::lean_dec(v_declName_4650_);
                    v_a_4698_ = crate::leanh::lean_ctor_get(v___x_4689_, 0);
                    v_isSharedCheck_4705_ = (!crate::leanh::lean_is_exclusive(v___x_4689_)) as u8;
                    if v_isSharedCheck_4705_ == 0 {
                        v___x_4700_ = v___x_4689_;
                        v_isShared_4701_ = v_isSharedCheck_4705_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4698_);
                        crate::leanh::lean_dec(v___x_4689_);
                        v___x_4700_ = crate::leanh::lean_box(0);
                        v_isShared_4701_ = v_isSharedCheck_4705_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4701_ == 0 {
                    v___x_4703_ = v___x_4700_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
                    v___x_4703_ = v_reuseFailAlloc_4704_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4703_;
            }
            6 => {
                v___x_4708_ = lean_nat_dec_lt(v_fst_4676_, v___y_4707_);
                if v___x_4708_ == 0 {
                    crate::leanh::lean_del_object(v___x_4679_);
                    crate::leanh::lean_del_object(v___x_4674_);
                    v___y_4684_ = v___y_4707_;
                    v___y_4685_ = v___y_4657_;
                    v___y_4686_ = v___y_4658_;
                    v___y_4687_ = v___y_4659_;
                    v___y_4688_ = v___y_4660_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_4707_);
                    crate::leanh::lean_dec(v___x_4682_);
                    crate::leanh::lean_dec(v_snd_4677_);
                    crate::leanh::lean_dec(v_fst_4676_);
                    crate::leanh::lean_dec(v_fst_4672_);
                    crate::leanh::lean_dec_ref(v_x_4655_);
                    crate::leanh::lean_dec_ref(v_x_4654_);
                    crate::leanh::lean_dec_ref(v_a_4653_);
                    crate::leanh::lean_dec_ref(v_xs_4652_);
                    v___x_4709_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1_once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
                    v___x_4710_ = 0;
                    v___x_4711_ = l_Lean_MessageData_ofConstName(v_declName_4650_, v___x_4710_);
                    if v_isShared_4680_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4679_, 7);
                        crate::leanh::lean_ctor_set(v___x_4679_, 1, v___x_4711_);
                        crate::leanh::lean_ctor_set(v___x_4679_, 0, v___x_4709_);
                        v___x_4713_ = v___x_4679_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4727_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4727_, 0, v___x_4709_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4727_, 1, v___x_4711_);
                        v___x_4713_ = v_reuseFailAlloc_4727_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4714_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___closed__1);
                if v_isShared_4675_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4674_, 7);
                    crate::leanh::lean_ctor_set(v___x_4674_, 1, v___x_4714_);
                    crate::leanh::lean_ctor_set(v___x_4674_, 0, v___x_4713_);
                    v___x_4716_ = v___x_4674_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4726_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4726_, 1, v___x_4714_);
                    v___x_4716_ = v_reuseFailAlloc_4726_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4717_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v___x_4716_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
                v_a_4718_ = crate::leanh::lean_ctor_get(v___x_4717_, 0);
                v_isSharedCheck_4725_ = (!crate::leanh::lean_is_exclusive(v___x_4717_)) as u8;
                if v_isSharedCheck_4725_ == 0 {
                    v___x_4720_ = v___x_4717_;
                    v_isShared_4721_ = v_isSharedCheck_4725_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4718_);
                    crate::leanh::lean_dec(v___x_4717_);
                    v___x_4720_ = crate::leanh::lean_box(0);
                    v_isShared_4721_ = v_isSharedCheck_4725_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4721_ == 0 {
                    v___x_4723_ = v___x_4720_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
                    v___x_4723_ = v_reuseFailAlloc_4724_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4723_;
            }
            11 => {
                if v_isShared_4738_ == 0 {
                    v___x_4740_ = v___x_4737_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4741_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
                    v___x_4740_ = v_reuseFailAlloc_4741_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4740_;
            }
            13 => {
                if v_isShared_4746_ == 0 {
                    v___x_4748_ = v___x_4745_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4749_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
                    v___x_4748_ = v_reuseFailAlloc_4749_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2___boxed(
    mut v_declName_4751_: *mut crate::leanh::LeanObject,
    mut v_a_4752_: *mut crate::leanh::LeanObject,
    mut v_xs_4753_: *mut crate::leanh::LeanObject,
    mut v_a_4754_: *mut crate::leanh::LeanObject,
    mut v_x_4755_: *mut crate::leanh::LeanObject,
    mut v_x_4756_: *mut crate::leanh::LeanObject,
    mut v_x_4757_: *mut crate::leanh::LeanObject,
    mut v___y_4758_: *mut crate::leanh::LeanObject,
    mut v___y_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(v_declName_4751_, v_a_4752_, v_xs_4753_, v_a_4754_, v_x_4755_, v_x_4756_, v_x_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
    crate::leanh::lean_dec(v___y_4761_);
    crate::leanh::lean_dec_ref(v___y_4760_);
    crate::leanh::lean_dec(v___y_4759_);
    crate::leanh::lean_dec_ref(v___y_4758_);
    return v_res_4763_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(
    mut v_declName_4764_: *mut crate::leanh::LeanObject,
    mut v_a_4765_: *mut crate::leanh::LeanObject,
    mut v_a_4766_: *mut crate::leanh::LeanObject,
    mut v_xs_4767_: *mut crate::leanh::LeanObject,
    mut v_type_4768_: *mut crate::leanh::LeanObject,
    mut v___y_4769_: *mut crate::leanh::LeanObject,
    mut v___y_4770_: *mut crate::leanh::LeanObject,
    mut v___y_4771_: *mut crate::leanh::LeanObject,
    mut v___y_4772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_4774_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__3___redArg___lam__0___closed__0);
    v_nargs_4775_ = l_Lean_Expr_getAppNumArgs(v_type_4768_);
    crate::leanh::lean_inc(v_nargs_4775_);
    v___x_4776_ = lean_mk_array(v_nargs_4775_, v_dummy_4774_);
    v___x_4777_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4778_ = lean_nat_sub(v_nargs_4775_, v___x_4777_);
    crate::leanh::lean_dec(v_nargs_4775_);
    v___x_4779_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__2(v_declName_4764_, v_a_4765_, v_xs_4767_, v_a_4766_, v_type_4768_, v___x_4776_, v___x_4778_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
    return v___x_4779_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0___boxed(
    mut v_declName_4780_: *mut crate::leanh::LeanObject,
    mut v_a_4781_: *mut crate::leanh::LeanObject,
    mut v_a_4782_: *mut crate::leanh::LeanObject,
    mut v_xs_4783_: *mut crate::leanh::LeanObject,
    mut v_type_4784_: *mut crate::leanh::LeanObject,
    mut v___y_4785_: *mut crate::leanh::LeanObject,
    mut v___y_4786_: *mut crate::leanh::LeanObject,
    mut v___y_4787_: *mut crate::leanh::LeanObject,
    mut v___y_4788_: *mut crate::leanh::LeanObject,
    mut v___y_4789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4790_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0(
        v_declName_4780_,
        v_a_4781_,
        v_a_4782_,
        v_xs_4783_,
        v_type_4784_,
        v___y_4785_,
        v___y_4786_,
        v___y_4787_,
        v___y_4788_,
    );
    crate::leanh::lean_dec(v___y_4788_);
    crate::leanh::lean_dec_ref(v___y_4787_);
    crate::leanh::lean_dec(v___y_4786_);
    crate::leanh::lean_dec_ref(v___y_4785_);
    return v_res_4790_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_4791_: *mut crate::leanh::LeanObject,
    mut v_msg_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4810_: u8 = 0;
    let mut v_cancelTk_x3f_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4812_: u8 = 0;
    let mut v_inheritedTraceOptions_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4798_ = crate::leanh::lean_ctor_get(v___y_4795_, 0);
    v_fileMap_4799_ = crate::leanh::lean_ctor_get(v___y_4795_, 1);
    v_options_4800_ = crate::leanh::lean_ctor_get(v___y_4795_, 2);
    v_currRecDepth_4801_ = crate::leanh::lean_ctor_get(v___y_4795_, 3);
    v_maxRecDepth_4802_ = crate::leanh::lean_ctor_get(v___y_4795_, 4);
    v_ref_4803_ = crate::leanh::lean_ctor_get(v___y_4795_, 5);
    v_currNamespace_4804_ = crate::leanh::lean_ctor_get(v___y_4795_, 6);
    v_openDecls_4805_ = crate::leanh::lean_ctor_get(v___y_4795_, 7);
    v_initHeartbeats_4806_ = crate::leanh::lean_ctor_get(v___y_4795_, 8);
    v_maxHeartbeats_4807_ = crate::leanh::lean_ctor_get(v___y_4795_, 9);
    v_quotContext_4808_ = crate::leanh::lean_ctor_get(v___y_4795_, 10);
    v_currMacroScope_4809_ = crate::leanh::lean_ctor_get(v___y_4795_, 11);
    v_diag_4810_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4795_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4811_ = crate::leanh::lean_ctor_get(v___y_4795_, 12);
    v_suppressElabErrors_4812_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4795_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4813_ = crate::leanh::lean_ctor_get(v___y_4795_, 13);
    v_ref_4814_ = l_Lean_replaceRef(v_ref_4791_, v_ref_4803_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4813_);
    crate::leanh::lean_inc(v_cancelTk_x3f_4811_);
    crate::leanh::lean_inc(v_currMacroScope_4809_);
    crate::leanh::lean_inc(v_quotContext_4808_);
    crate::leanh::lean_inc(v_maxHeartbeats_4807_);
    crate::leanh::lean_inc(v_initHeartbeats_4806_);
    crate::leanh::lean_inc(v_openDecls_4805_);
    crate::leanh::lean_inc(v_currNamespace_4804_);
    crate::leanh::lean_inc(v_maxRecDepth_4802_);
    crate::leanh::lean_inc(v_currRecDepth_4801_);
    crate::leanh::lean_inc_ref(v_options_4800_);
    crate::leanh::lean_inc_ref(v_fileMap_4799_);
    crate::leanh::lean_inc_ref(v_fileName_4798_);
    v___x_4815_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_4815_, 0, v_fileName_4798_);
    crate::leanh::lean_ctor_set(v___x_4815_, 1, v_fileMap_4799_);
    crate::leanh::lean_ctor_set(v___x_4815_, 2, v_options_4800_);
    crate::leanh::lean_ctor_set(v___x_4815_, 3, v_currRecDepth_4801_);
    crate::leanh::lean_ctor_set(v___x_4815_, 4, v_maxRecDepth_4802_);
    crate::leanh::lean_ctor_set(v___x_4815_, 5, v_ref_4814_);
    crate::leanh::lean_ctor_set(v___x_4815_, 6, v_currNamespace_4804_);
    crate::leanh::lean_ctor_set(v___x_4815_, 7, v_openDecls_4805_);
    crate::leanh::lean_ctor_set(v___x_4815_, 8, v_initHeartbeats_4806_);
    crate::leanh::lean_ctor_set(v___x_4815_, 9, v_maxHeartbeats_4807_);
    crate::leanh::lean_ctor_set(v___x_4815_, 10, v_quotContext_4808_);
    crate::leanh::lean_ctor_set(v___x_4815_, 11, v_currMacroScope_4809_);
    crate::leanh::lean_ctor_set(v___x_4815_, 12, v_cancelTk_x3f_4811_);
    crate::leanh::lean_ctor_set(v___x_4815_, 13, v_inheritedTraceOptions_4813_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4815_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_4810_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4815_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4812_,
    );
    v___x_4816_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0_spec__0___redArg(v_msg_4792_, v___y_4793_, v___y_4794_, v___x_4815_, v___y_4796_);
    crate::leanh::lean_dec_ref_known(v___x_4815_, 14);
    return v___x_4816_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_4817_: *mut crate::leanh::LeanObject,
    mut v_msg_4818_: *mut crate::leanh::LeanObject,
    mut v___y_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
    mut v___y_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4824_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_4817_, v_msg_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
    crate::leanh::lean_dec(v___y_4822_);
    crate::leanh::lean_dec_ref(v___y_4821_);
    crate::leanh::lean_dec(v___y_4820_);
    crate::leanh::lean_dec_ref(v___y_4819_);
    crate::leanh::lean_dec(v_ref_4817_);
    return v_res_4824_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4825_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4826_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
    v___x_4827_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4827_, 0, v___x_4826_);
    return v___x_4827_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_4829_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4830_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4830_, 0, v___x_4829_);
    crate::leanh::lean_ctor_set(v___x_4830_, 1, v___x_4829_);
    crate::leanh::lean_ctor_set(v___x_4830_, 2, v___x_4829_);
    crate::leanh::lean_ctor_set(v___x_4830_, 3, v___x_4829_);
    crate::leanh::lean_ctor_set(v___x_4830_, 4, v___x_4828_);
    crate::leanh::lean_ctor_set(v___x_4830_, 5, v___x_4828_);
    crate::leanh::lean_ctor_set(v___x_4830_, 6, v___x_4828_);
    crate::leanh::lean_ctor_set(v___x_4830_, 7, v___x_4828_);
    crate::leanh::lean_ctor_set(v___x_4830_, 8, v___x_4828_);
    crate::leanh::lean_ctor_set(v___x_4830_, 9, v___x_4828_);
    return v___x_4830_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4832_ = lean_mk_empty_array_with_capacity(v___x_4831_);
    v___x_4833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4833_, 0, v___x_4832_);
    return v___x_4833_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4834_: usize = 0;
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4834_ = 5usize;
    v___x_4835_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4836_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4837_ = lean_mk_empty_array_with_capacity(v___x_4836_);
    v___x_4838_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
    v___x_4839_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4839_, 0, v___x_4838_);
    crate::leanh::lean_ctor_set(v___x_4839_, 1, v___x_4837_);
    crate::leanh::lean_ctor_set(v___x_4839_, 2, v___x_4835_);
    crate::leanh::lean_ctor_set(v___x_4839_, 3, v___x_4835_);
    crate::leanh::lean_ctor_set_usize(v___x_4839_, 4, v___x_4834_);
    return v___x_4839_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4840_ = crate::leanh::lean_box(1);
    v___x_4841_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_4842_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_4843_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4843_, 0, v___x_4842_);
    crate::leanh::lean_ctor_set(v___x_4843_, 1, v___x_4841_);
    crate::leanh::lean_ctor_set(v___x_4843_, 2, v___x_4840_);
    return v___x_4843_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4845_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_4846_ = l_Lean_stringToMessageData(v___x_4845_);
    return v___x_4846_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4848_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_4849_ = l_Lean_stringToMessageData(v___x_4848_);
    return v___x_4849_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4851_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_4852_ = l_Lean_stringToMessageData(v___x_4851_);
    return v___x_4852_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4854_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_4855_ = l_Lean_stringToMessageData(v___x_4854_);
    return v___x_4855_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4857_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14;
    v___x_4858_ = l_Lean_stringToMessageData(v___x_4857_);
    return v___x_4858_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4860_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16;
    v___x_4861_ = l_Lean_stringToMessageData(v___x_4860_);
    return v___x_4861_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4863_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18;
    v___x_4864_ = l_Lean_stringToMessageData(v___x_4863_);
    return v___x_4864_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_4865_: *mut crate::leanh::LeanObject,
    mut v_declHint_4866_: *mut crate::leanh::LeanObject,
    mut v___y_4867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: u8 = 0;
    let mut v_isExporting_4872_: u8 = 0;
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: u8 = 0;
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4894_: u8 = 0;
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: u8 = 0;
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4926_: u8 = 0;
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4869_ = lean_st_ref_get(v___y_4867_);
                v_env_4870_ = crate::leanh::lean_ctor_get(v___x_4869_, 0);
                crate::leanh::lean_inc_ref(v_env_4870_);
                crate::leanh::lean_dec(v___x_4869_);
                v___x_4871_ = l_Lean_Name_isAnonymous(v_declHint_4866_);
                if v___x_4871_ == 0 {
                    v_isExporting_4872_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_4870_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4872_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_4870_);
                        crate::leanh::lean_dec(v_declHint_4866_);
                        v___x_4873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4873_, 0, v_msg_4865_);
                        return v___x_4873_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_4870_);
                        v___x_4874_ = l_Lean_Environment_setExporting(v_env_4870_, v___x_4871_);
                        crate::leanh::lean_inc(v_declHint_4866_);
                        crate::leanh::lean_inc_ref(v___x_4874_);
                        v___x_4875_ = l_Lean_Environment_contains(
                            v___x_4874_,
                            v_declHint_4866_,
                            v_isExporting_4872_,
                        );
                        if v___x_4875_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4874_);
                            crate::leanh::lean_dec_ref(v_env_4870_);
                            crate::leanh::lean_dec(v_declHint_4866_);
                            v___x_4876_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4876_, 0, v_msg_4865_);
                            return v___x_4876_;
                        } else {
                            v___x_4877_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
                            v___x_4878_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                            v___x_4879_ = l_Lean_Options_empty;
                            v___x_4880_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_4874_);
                            crate::leanh::lean_ctor_set(v___x_4880_, 1, v___x_4877_);
                            crate::leanh::lean_ctor_set(v___x_4880_, 2, v___x_4878_);
                            crate::leanh::lean_ctor_set(v___x_4880_, 3, v___x_4879_);
                            crate::leanh::lean_inc(v_declHint_4866_);
                            v___x_4881_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4866_, v___x_4871_);
                            v_c_4882_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_4882_, 0, v___x_4880_);
                            crate::leanh::lean_ctor_set(v_c_4882_, 1, v___x_4881_);
                            v___x_4883_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4870_,
                                v_declHint_4866_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4883_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_4870_);
                                crate::leanh::lean_dec(v_declHint_4866_);
                                v___x_4884_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                                v___x_4885_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4885_, 0, v___x_4884_);
                                crate::leanh::lean_ctor_set(v___x_4885_, 1, v_c_4882_);
                                v___x_4886_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                                v___x_4887_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4887_, 0, v___x_4885_);
                                crate::leanh::lean_ctor_set(v___x_4887_, 1, v___x_4886_);
                                v___x_4888_ = l_Lean_MessageData_note(v___x_4887_);
                                v___x_4889_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4889_, 0, v_msg_4865_);
                                crate::leanh::lean_ctor_set(v___x_4889_, 1, v___x_4888_);
                                v___x_4890_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4890_, 0, v___x_4889_);
                                return v___x_4890_;
                            } else {
                                v_val_4891_ = crate::leanh::lean_ctor_get(v___x_4883_, 0);
                                v_isSharedCheck_4926_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4883_)) as u8;
                                if v_isSharedCheck_4926_ == 0 {
                                    v___x_4893_ = v___x_4883_;
                                    v_isShared_4894_ = v_isSharedCheck_4926_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_4891_);
                                    crate::leanh::lean_dec(v___x_4883_);
                                    v___x_4893_ = crate::leanh::lean_box(0);
                                    v_isShared_4894_ = v_isSharedCheck_4926_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_4870_);
                    crate::leanh::lean_dec(v_declHint_4866_);
                    v___x_4927_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4927_, 0, v_msg_4865_);
                    return v___x_4927_;
                }
            }
            1 => {
                v___x_4895_ = crate::leanh::lean_box(0);
                v___x_4896_ = l_Lean_Environment_header(v_env_4870_);
                crate::leanh::lean_dec_ref(v_env_4870_);
                v___x_4897_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4896_);
                v_mod_4898_ = lean_array_get(v___x_4895_, v___x_4897_, v_val_4891_);
                crate::leanh::lean_dec(v_val_4891_);
                crate::leanh::lean_dec_ref(v___x_4897_);
                v___x_4899_ = l_Lean_isPrivateName(v_declHint_4866_);
                crate::leanh::lean_dec(v_declHint_4866_);
                if v___x_4899_ == 0 {
                    v___x_4900_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_4901_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4901_, 0, v___x_4900_);
                    crate::leanh::lean_ctor_set(v___x_4901_, 1, v_c_4882_);
                    v___x_4902_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_4903_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4903_, 0, v___x_4901_);
                    crate::leanh::lean_ctor_set(v___x_4903_, 1, v___x_4902_);
                    v___x_4904_ = l_Lean_MessageData_ofName(v_mod_4898_);
                    v___x_4905_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4905_, 0, v___x_4903_);
                    crate::leanh::lean_ctor_set(v___x_4905_, 1, v___x_4904_);
                    v___x_4906_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
                    v___x_4907_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4907_, 0, v___x_4905_);
                    crate::leanh::lean_ctor_set(v___x_4907_, 1, v___x_4906_);
                    v___x_4908_ = l_Lean_MessageData_note(v___x_4907_);
                    v___x_4909_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4909_, 0, v_msg_4865_);
                    crate::leanh::lean_ctor_set(v___x_4909_, 1, v___x_4908_);
                    if v_isShared_4894_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4893_, 0);
                        crate::leanh::lean_ctor_set(v___x_4893_, 0, v___x_4909_);
                        v___x_4911_ = v___x_4893_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4912_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
                        v___x_4911_ = v_reuseFailAlloc_4912_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4913_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_4914_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4914_, 0, v___x_4913_);
                    crate::leanh::lean_ctor_set(v___x_4914_, 1, v_c_4882_);
                    v___x_4915_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
                    v___x_4916_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4916_, 0, v___x_4914_);
                    crate::leanh::lean_ctor_set(v___x_4916_, 1, v___x_4915_);
                    v___x_4917_ = l_Lean_MessageData_ofName(v_mod_4898_);
                    v___x_4918_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4918_, 0, v___x_4916_);
                    crate::leanh::lean_ctor_set(v___x_4918_, 1, v___x_4917_);
                    v___x_4919_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
                    v___x_4920_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4920_, 0, v___x_4918_);
                    crate::leanh::lean_ctor_set(v___x_4920_, 1, v___x_4919_);
                    v___x_4921_ = l_Lean_MessageData_note(v___x_4920_);
                    v___x_4922_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4922_, 0, v_msg_4865_);
                    crate::leanh::lean_ctor_set(v___x_4922_, 1, v___x_4921_);
                    if v_isShared_4894_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4893_, 0);
                        crate::leanh::lean_ctor_set(v___x_4893_, 0, v___x_4922_);
                        v___x_4924_ = v___x_4893_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4922_);
                        v___x_4924_ = v_reuseFailAlloc_4925_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4911_;
            }
            3 => {
                return v___x_4924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_4928_: *mut crate::leanh::LeanObject,
    mut v_declHint_4929_: *mut crate::leanh::LeanObject,
    mut v___y_4930_: *mut crate::leanh::LeanObject,
    mut v___y_4931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4932_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4928_, v_declHint_4929_, v___y_4930_);
    crate::leanh::lean_dec(v___y_4930_);
    return v_res_4932_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_4933_: *mut crate::leanh::LeanObject,
    mut v_declHint_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
    mut v___y_4937_: *mut crate::leanh::LeanObject,
    mut v___y_4938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4940_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4933_, v_declHint_4934_, v___y_4938_);
                v_a_4941_ = crate::leanh::lean_ctor_get(v___x_4940_, 0);
                v_isSharedCheck_4950_ = (!crate::leanh::lean_is_exclusive(v___x_4940_)) as u8;
                if v_isSharedCheck_4950_ == 0 {
                    v___x_4943_ = v___x_4940_;
                    v_isShared_4944_ = v_isSharedCheck_4950_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4941_);
                    crate::leanh::lean_dec(v___x_4940_);
                    v___x_4943_ = crate::leanh::lean_box(0);
                    v_isShared_4944_ = v_isSharedCheck_4950_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4945_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4946_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4946_, 0, v___x_4945_);
                crate::leanh::lean_ctor_set(v___x_4946_, 1, v_a_4941_);
                if v_isShared_4944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4943_, 0, v___x_4946_);
                    v___x_4948_ = v___x_4943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4946_);
                    v___x_4948_ = v_reuseFailAlloc_4949_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v_msg_4951_: *mut crate::leanh::LeanObject,
    mut v_declHint_4952_: *mut crate::leanh::LeanObject,
    mut v___y_4953_: *mut crate::leanh::LeanObject,
    mut v___y_4954_: *mut crate::leanh::LeanObject,
    mut v___y_4955_: *mut crate::leanh::LeanObject,
    mut v___y_4956_: *mut crate::leanh::LeanObject,
    mut v___y_4957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4958_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_4951_, v_declHint_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_);
    crate::leanh::lean_dec(v___y_4956_);
    crate::leanh::lean_dec_ref(v___y_4955_);
    crate::leanh::lean_dec(v___y_4954_);
    crate::leanh::lean_dec_ref(v___y_4953_);
    return v_res_4958_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_4959_: *mut crate::leanh::LeanObject,
    mut v_msg_4960_: *mut crate::leanh::LeanObject,
    mut v_declHint_4961_: *mut crate::leanh::LeanObject,
    mut v___y_4962_: *mut crate::leanh::LeanObject,
    mut v___y_4963_: *mut crate::leanh::LeanObject,
    mut v___y_4964_: *mut crate::leanh::LeanObject,
    mut v___y_4965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4967_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_4960_, v_declHint_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
    v_a_4968_ = crate::leanh::lean_ctor_get(v___x_4967_, 0);
    crate::leanh::lean_inc(v_a_4968_);
    crate::leanh::lean_dec_ref(v___x_4967_);
    v___x_4969_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_4959_, v_a_4968_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
    return v___x_4969_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_4970_: *mut crate::leanh::LeanObject,
    mut v_msg_4971_: *mut crate::leanh::LeanObject,
    mut v_declHint_4972_: *mut crate::leanh::LeanObject,
    mut v___y_4973_: *mut crate::leanh::LeanObject,
    mut v___y_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
    mut v___y_4977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4978_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_4970_, v_msg_4971_, v_declHint_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
    crate::leanh::lean_dec(v___y_4976_);
    crate::leanh::lean_dec_ref(v___y_4975_);
    crate::leanh::lean_dec(v___y_4974_);
    crate::leanh::lean_dec_ref(v___y_4973_);
    crate::leanh::lean_dec(v_ref_4970_);
    return v_res_4978_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4980_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_4981_ = l_Lean_stringToMessageData(v___x_4980_);
    return v___x_4981_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(
    mut v_ref_4982_: *mut crate::leanh::LeanObject,
    mut v_constName_4983_: *mut crate::leanh::LeanObject,
    mut v___y_4984_: *mut crate::leanh::LeanObject,
    mut v___y_4985_: *mut crate::leanh::LeanObject,
    mut v___y_4986_: *mut crate::leanh::LeanObject,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u8 = 0;
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4989_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_4990_ = 0;
    crate::leanh::lean_inc(v_constName_4983_);
    v___x_4991_ = l_Lean_MessageData_ofConstName(v_constName_4983_, v___x_4990_);
    v___x_4992_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4992_, 0, v___x_4989_);
    crate::leanh::lean_ctor_set(v___x_4992_, 1, v___x_4991_);
    v___x_4993_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f_spec__0___closed__1);
    v___x_4994_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4994_, 0, v___x_4992_);
    crate::leanh::lean_ctor_set(v___x_4994_, 1, v___x_4993_);
    v___x_4995_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_4982_, v___x_4994_, v_constName_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
    return v___x_4995_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4996_: *mut crate::leanh::LeanObject,
    mut v_constName_4997_: *mut crate::leanh::LeanObject,
    mut v___y_4998_: *mut crate::leanh::LeanObject,
    mut v___y_4999_: *mut crate::leanh::LeanObject,
    mut v___y_5000_: *mut crate::leanh::LeanObject,
    mut v___y_5001_: *mut crate::leanh::LeanObject,
    mut v___y_5002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5003_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_4996_, v_constName_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
    crate::leanh::lean_dec(v___y_5001_);
    crate::leanh::lean_dec_ref(v___y_5000_);
    crate::leanh::lean_dec(v___y_4999_);
    crate::leanh::lean_dec_ref(v___y_4998_);
    crate::leanh::lean_dec(v_ref_4996_);
    return v_res_5003_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(
    mut v_constName_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5010_ = crate::leanh::lean_ctor_get(v___y_5007_, 5);
    v___x_5011_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_5010_, v_constName_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
    return v___x_5011_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg___boxed(
    mut v_constName_5012_: *mut crate::leanh::LeanObject,
    mut v___y_5013_: *mut crate::leanh::LeanObject,
    mut v___y_5014_: *mut crate::leanh::LeanObject,
    mut v___y_5015_: *mut crate::leanh::LeanObject,
    mut v___y_5016_: *mut crate::leanh::LeanObject,
    mut v___y_5017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5018_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
    crate::leanh::lean_dec(v___y_5016_);
    crate::leanh::lean_dec_ref(v___y_5015_);
    crate::leanh::lean_dec(v___y_5014_);
    crate::leanh::lean_dec_ref(v___y_5013_);
    return v_res_5018_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(
    mut v_constName_5019_: *mut crate::leanh::LeanObject,
    mut v___y_5020_: *mut crate::leanh::LeanObject,
    mut v___y_5021_: *mut crate::leanh::LeanObject,
    mut v___y_5022_: *mut crate::leanh::LeanObject,
    mut v___y_5023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: u8 = 0;
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5033_: u8 = 0;
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5025_ = lean_st_ref_get(v___y_5023_);
                v_env_5026_ = crate::leanh::lean_ctor_get(v___x_5025_, 0);
                crate::leanh::lean_inc_ref(v_env_5026_);
                crate::leanh::lean_dec(v___x_5025_);
                v___x_5027_ = 0;
                crate::leanh::lean_inc(v_constName_5019_);
                v___x_5028_ =
                    l_Lean_Environment_find_x3f(v_env_5026_, v_constName_5019_, v___x_5027_);
                if crate::leanh::lean_obj_tag(v___x_5028_) == 0 {
                    v___x_5029_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
                    return v___x_5029_;
                } else {
                    crate::leanh::lean_dec(v_constName_5019_);
                    v_val_5030_ = crate::leanh::lean_ctor_get(v___x_5028_, 0);
                    v_isSharedCheck_5037_ = (!crate::leanh::lean_is_exclusive(v___x_5028_)) as u8;
                    if v_isSharedCheck_5037_ == 0 {
                        v___x_5032_ = v___x_5028_;
                        v_isShared_5033_ = v_isSharedCheck_5037_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5030_);
                        crate::leanh::lean_dec(v___x_5028_);
                        v___x_5032_ = crate::leanh::lean_box(0);
                        v_isShared_5033_ = v_isSharedCheck_5037_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5033_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5032_, 0);
                    v___x_5035_ = v___x_5032_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_val_5030_);
                    v___x_5035_ = v_reuseFailAlloc_5036_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0___boxed(
    mut v_constName_5038_: *mut crate::leanh::LeanObject,
    mut v___y_5039_: *mut crate::leanh::LeanObject,
    mut v___y_5040_: *mut crate::leanh::LeanObject,
    mut v___y_5041_: *mut crate::leanh::LeanObject,
    mut v___y_5042_: *mut crate::leanh::LeanObject,
    mut v___y_5043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5044_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(v_constName_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
    crate::leanh::lean_dec(v___y_5042_);
    crate::leanh::lean_dec_ref(v___y_5041_);
    crate::leanh::lean_dec(v___y_5040_);
    crate::leanh::lean_dec_ref(v___y_5039_);
    return v_res_5044_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(
    mut v_declName_5045_: *mut crate::leanh::LeanObject,
    mut v_majorPos_x3f_5046_: *mut crate::leanh::LeanObject,
    mut v_a_5047_: *mut crate::leanh::LeanObject,
    mut v_a_5048_: *mut crate::leanh::LeanObject,
    mut v_a_5049_: *mut crate::leanh::LeanObject,
    mut v_a_5050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: u8 = 0;
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5067_: u8 = 0;
    let mut v_a_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5071_: u8 = 0;
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_5045_);
                v___x_5052_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0(v_declName_5045_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
                if crate::leanh::lean_obj_tag(v___x_5052_) == 0 {
                    v_a_5053_ = crate::leanh::lean_ctor_get(v___x_5052_, 0);
                    crate::leanh::lean_inc(v_a_5053_);
                    crate::leanh::lean_dec_ref_known(v___x_5052_, 1);
                    crate::leanh::lean_inc(v_declName_5045_);
                    v___x_5054_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(v_declName_5045_, v_majorPos_x3f_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
                    if crate::leanh::lean_obj_tag(v___x_5054_) == 0 {
                        v_a_5055_ = crate::leanh::lean_ctor_get(v___x_5054_, 0);
                        crate::leanh::lean_inc(v_a_5055_);
                        crate::leanh::lean_dec_ref_known(v___x_5054_, 1);
                        crate::leanh::lean_inc(v_a_5053_);
                        v___f_5056_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                        crate::leanh::lean_closure_set(v___f_5056_, 0, v_declName_5045_);
                        crate::leanh::lean_closure_set(v___f_5056_, 1, v_a_5055_);
                        crate::leanh::lean_closure_set(v___f_5056_, 2, v_a_5053_);
                        v___x_5057_ = l_Lean_ConstantInfo_type(v_a_5053_);
                        crate::leanh::lean_dec(v_a_5053_);
                        v___x_5058_ = 0;
                        v___x_5059_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive_spec__2___redArg(v___x_5057_, v___f_5056_, v___x_5058_, v___x_5058_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
                        return v___x_5059_;
                    } else {
                        crate::leanh::lean_dec(v_a_5053_);
                        crate::leanh::lean_dec(v_declName_5045_);
                        v_a_5060_ = crate::leanh::lean_ctor_get(v___x_5054_, 0);
                        v_isSharedCheck_5067_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5054_)) as u8;
                        if v_isSharedCheck_5067_ == 0 {
                            v___x_5062_ = v___x_5054_;
                            v_isShared_5063_ = v_isSharedCheck_5067_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5060_);
                            crate::leanh::lean_dec(v___x_5054_);
                            v___x_5062_ = crate::leanh::lean_box(0);
                            v_isShared_5063_ = v_isSharedCheck_5067_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_majorPos_x3f_5046_);
                    crate::leanh::lean_dec(v_declName_5045_);
                    v_a_5068_ = crate::leanh::lean_ctor_get(v___x_5052_, 0);
                    v_isSharedCheck_5075_ = (!crate::leanh::lean_is_exclusive(v___x_5052_)) as u8;
                    if v_isSharedCheck_5075_ == 0 {
                        v___x_5070_ = v___x_5052_;
                        v_isShared_5071_ = v_isSharedCheck_5075_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5068_);
                        crate::leanh::lean_dec(v___x_5052_);
                        v___x_5070_ = crate::leanh::lean_box(0);
                        v_isShared_5071_ = v_isSharedCheck_5075_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5063_ == 0 {
                    v___x_5065_ = v___x_5062_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
                    v___x_5065_ = v_reuseFailAlloc_5066_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5065_;
            }
            3 => {
                if v_isShared_5071_ == 0 {
                    v___x_5073_ = v___x_5070_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
                    v___x_5073_ = v_reuseFailAlloc_5074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___boxed(
    mut v_declName_5076_: *mut crate::leanh::LeanObject,
    mut v_majorPos_x3f_5077_: *mut crate::leanh::LeanObject,
    mut v_a_5078_: *mut crate::leanh::LeanObject,
    mut v_a_5079_: *mut crate::leanh::LeanObject,
    mut v_a_5080_: *mut crate::leanh::LeanObject,
    mut v_a_5081_: *mut crate::leanh::LeanObject,
    mut v_a_5082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5083_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(
        v_declName_5076_,
        v_majorPos_x3f_5077_,
        v_a_5078_,
        v_a_5079_,
        v_a_5080_,
        v_a_5081_,
    );
    crate::leanh::lean_dec(v_a_5081_);
    crate::leanh::lean_dec_ref(v_a_5080_);
    crate::leanh::lean_dec(v_a_5079_);
    crate::leanh::lean_dec_ref(v_a_5078_);
    return v_res_5083_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(
    mut v_00_u03b1_5084_: *mut crate::leanh::LeanObject,
    mut v_constName_5085_: *mut crate::leanh::LeanObject,
    mut v___y_5086_: *mut crate::leanh::LeanObject,
    mut v___y_5087_: *mut crate::leanh::LeanObject,
    mut v___y_5088_: *mut crate::leanh::LeanObject,
    mut v___y_5089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5091_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___redArg(v_constName_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
    return v___x_5091_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0___boxed(
    mut v_00_u03b1_5092_: *mut crate::leanh::LeanObject,
    mut v_constName_5093_: *mut crate::leanh::LeanObject,
    mut v___y_5094_: *mut crate::leanh::LeanObject,
    mut v___y_5095_: *mut crate::leanh::LeanObject,
    mut v___y_5096_: *mut crate::leanh::LeanObject,
    mut v___y_5097_: *mut crate::leanh::LeanObject,
    mut v___y_5098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5099_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0(v_00_u03b1_5092_, v_constName_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
    crate::leanh::lean_dec(v___y_5097_);
    crate::leanh::lean_dec_ref(v___y_5096_);
    crate::leanh::lean_dec(v___y_5095_);
    crate::leanh::lean_dec_ref(v___y_5094_);
    return v_res_5099_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5100_: *mut crate::leanh::LeanObject,
    mut v_ref_5101_: *mut crate::leanh::LeanObject,
    mut v_constName_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5108_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___redArg(v_ref_5101_, v_constName_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
    return v___x_5108_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5109_: *mut crate::leanh::LeanObject,
    mut v_ref_5110_: *mut crate::leanh::LeanObject,
    mut v_constName_5111_: *mut crate::leanh::LeanObject,
    mut v___y_5112_: *mut crate::leanh::LeanObject,
    mut v___y_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5117_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1(v_00_u03b1_5109_, v_ref_5110_, v_constName_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_);
    crate::leanh::lean_dec(v___y_5115_);
    crate::leanh::lean_dec_ref(v___y_5114_);
    crate::leanh::lean_dec(v___y_5113_);
    crate::leanh::lean_dec_ref(v___y_5112_);
    crate::leanh::lean_dec(v_ref_5110_);
    return v_res_5117_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_5118_: *mut crate::leanh::LeanObject,
    mut v_ref_5119_: *mut crate::leanh::LeanObject,
    mut v_msg_5120_: *mut crate::leanh::LeanObject,
    mut v_declHint_5121_: *mut crate::leanh::LeanObject,
    mut v___y_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5127_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5119_, v_msg_5120_, v_declHint_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
    return v___x_5127_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_5128_: *mut crate::leanh::LeanObject,
    mut v_ref_5129_: *mut crate::leanh::LeanObject,
    mut v_msg_5130_: *mut crate::leanh::LeanObject,
    mut v_declHint_5131_: *mut crate::leanh::LeanObject,
    mut v___y_5132_: *mut crate::leanh::LeanObject,
    mut v___y_5133_: *mut crate::leanh::LeanObject,
    mut v___y_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5137_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5128_, v_ref_5129_, v_msg_5130_, v_declHint_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
    crate::leanh::lean_dec(v___y_5135_);
    crate::leanh::lean_dec_ref(v___y_5134_);
    crate::leanh::lean_dec(v___y_5133_);
    crate::leanh::lean_dec_ref(v___y_5132_);
    crate::leanh::lean_dec(v_ref_5129_);
    return v_res_5137_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_5138_: *mut crate::leanh::LeanObject,
    mut v_declHint_5139_: *mut crate::leanh::LeanObject,
    mut v___y_5140_: *mut crate::leanh::LeanObject,
    mut v___y_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5138_, v_declHint_5139_, v___y_5143_);
    return v___x_5145_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_5146_: *mut crate::leanh::LeanObject,
    mut v_declHint_5147_: *mut crate::leanh::LeanObject,
    mut v___y_5148_: *mut crate::leanh::LeanObject,
    mut v___y_5149_: *mut crate::leanh::LeanObject,
    mut v___y_5150_: *mut crate::leanh::LeanObject,
    mut v___y_5151_: *mut crate::leanh::LeanObject,
    mut v___y_5152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5153_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5146_, v_declHint_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_);
    crate::leanh::lean_dec(v___y_5151_);
    crate::leanh::lean_dec_ref(v___y_5150_);
    crate::leanh::lean_dec(v___y_5149_);
    crate::leanh::lean_dec_ref(v___y_5148_);
    return v_res_5153_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_5154_: *mut crate::leanh::LeanObject,
    mut v_ref_5155_: *mut crate::leanh::LeanObject,
    mut v_msg_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
    mut v___y_5160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5162_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5155_, v_msg_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
    return v___x_5162_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_5163_: *mut crate::leanh::LeanObject,
    mut v_ref_5164_: *mut crate::leanh::LeanObject,
    mut v_msg_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
    mut v___y_5168_: *mut crate::leanh::LeanObject,
    mut v___y_5169_: *mut crate::leanh::LeanObject,
    mut v___y_5170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5171_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5163_, v_ref_5164_, v_msg_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
    crate::leanh::lean_dec(v___y_5169_);
    crate::leanh::lean_dec_ref(v___y_5168_);
    crate::leanh::lean_dec(v___y_5167_);
    crate::leanh::lean_dec_ref(v___y_5166_);
    crate::leanh::lean_dec(v_ref_5164_);
    return v_res_5171_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(
    mut v_msgData_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5176_ = lean_st_ref_get(v___y_5174_);
    v_env_5177_ = crate::leanh::lean_ctor_get(v___x_5176_, 0);
    crate::leanh::lean_inc_ref(v_env_5177_);
    crate::leanh::lean_dec(v___x_5176_);
    v_options_5178_ = crate::leanh::lean_ctor_get(v___y_5173_, 2);
    v___x_5179_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
    v___x_5180_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5181_ = lean_mk_empty_array_with_capacity(v___x_5180_);
    crate::leanh::lean_dec_ref(v___x_5181_);
    v___x_5182_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
    crate::leanh::lean_inc_ref(v_options_5178_);
    v___x_5183_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5183_, 0, v_env_5177_);
    crate::leanh::lean_ctor_set(v___x_5183_, 1, v___x_5179_);
    crate::leanh::lean_ctor_set(v___x_5183_, 2, v___x_5182_);
    crate::leanh::lean_ctor_set(v___x_5183_, 3, v_options_5178_);
    v___x_5184_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5184_, 0, v___x_5183_);
    crate::leanh::lean_ctor_set(v___x_5184_, 1, v_msgData_5172_);
    v___x_5185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5185_, 0, v___x_5184_);
    return v___x_5185_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
    mut v___y_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5190_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(v_msgData_5186_, v___y_5187_, v___y_5188_);
    crate::leanh::lean_dec(v___y_5188_);
    crate::leanh::lean_dec_ref(v___y_5187_);
    return v_res_5190_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(
    mut v_msg_5191_: *mut crate::leanh::LeanObject,
    mut v___y_5192_: *mut crate::leanh::LeanObject,
    mut v___y_5193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5200_: u8 = 0;
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5195_ = crate::leanh::lean_ctor_get(v___y_5192_, 5);
                v___x_5196_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0_spec__1(v_msg_5191_, v___y_5192_, v___y_5193_);
                v_a_5197_ = crate::leanh::lean_ctor_get(v___x_5196_, 0);
                v_isSharedCheck_5205_ = (!crate::leanh::lean_is_exclusive(v___x_5196_)) as u8;
                if v_isSharedCheck_5205_ == 0 {
                    v___x_5199_ = v___x_5196_;
                    v_isShared_5200_ = v_isSharedCheck_5205_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5197_);
                    crate::leanh::lean_dec(v___x_5196_);
                    v___x_5199_ = crate::leanh::lean_box(0);
                    v_isShared_5200_ = v_isSharedCheck_5205_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5195_);
                v___x_5201_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5201_, 0, v_ref_5195_);
                crate::leanh::lean_ctor_set(v___x_5201_, 1, v_a_5197_);
                if v_isShared_5200_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5199_, 1);
                    crate::leanh::lean_ctor_set(v___x_5199_, 0, v___x_5201_);
                    v___x_5203_ = v___x_5199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v___x_5201_);
                    v___x_5203_ = v_reuseFailAlloc_5204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5203_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg___boxed(
    mut v_msg_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5210_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_5206_, v___y_5207_, v___y_5208_);
    crate::leanh::lean_dec(v___y_5208_);
    crate::leanh::lean_dec_ref(v___y_5207_);
    return v_res_5210_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(
    mut v_ref_5211_: *mut crate::leanh::LeanObject,
    mut v_msg_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5228_: u8 = 0;
    let mut v_cancelTk_x3f_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5230_: u8 = 0;
    let mut v_inheritedTraceOptions_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5216_ = crate::leanh::lean_ctor_get(v___y_5213_, 0);
    v_fileMap_5217_ = crate::leanh::lean_ctor_get(v___y_5213_, 1);
    v_options_5218_ = crate::leanh::lean_ctor_get(v___y_5213_, 2);
    v_currRecDepth_5219_ = crate::leanh::lean_ctor_get(v___y_5213_, 3);
    v_maxRecDepth_5220_ = crate::leanh::lean_ctor_get(v___y_5213_, 4);
    v_ref_5221_ = crate::leanh::lean_ctor_get(v___y_5213_, 5);
    v_currNamespace_5222_ = crate::leanh::lean_ctor_get(v___y_5213_, 6);
    v_openDecls_5223_ = crate::leanh::lean_ctor_get(v___y_5213_, 7);
    v_initHeartbeats_5224_ = crate::leanh::lean_ctor_get(v___y_5213_, 8);
    v_maxHeartbeats_5225_ = crate::leanh::lean_ctor_get(v___y_5213_, 9);
    v_quotContext_5226_ = crate::leanh::lean_ctor_get(v___y_5213_, 10);
    v_currMacroScope_5227_ = crate::leanh::lean_ctor_get(v___y_5213_, 11);
    v_diag_5228_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5213_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5229_ = crate::leanh::lean_ctor_get(v___y_5213_, 12);
    v_suppressElabErrors_5230_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5213_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5231_ = crate::leanh::lean_ctor_get(v___y_5213_, 13);
    v_ref_5232_ = l_Lean_replaceRef(v_ref_5211_, v_ref_5221_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5231_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5229_);
    crate::leanh::lean_inc(v_currMacroScope_5227_);
    crate::leanh::lean_inc(v_quotContext_5226_);
    crate::leanh::lean_inc(v_maxHeartbeats_5225_);
    crate::leanh::lean_inc(v_initHeartbeats_5224_);
    crate::leanh::lean_inc(v_openDecls_5223_);
    crate::leanh::lean_inc(v_currNamespace_5222_);
    crate::leanh::lean_inc(v_maxRecDepth_5220_);
    crate::leanh::lean_inc(v_currRecDepth_5219_);
    crate::leanh::lean_inc_ref(v_options_5218_);
    crate::leanh::lean_inc_ref(v_fileMap_5217_);
    crate::leanh::lean_inc_ref(v_fileName_5216_);
    v___x_5233_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5233_, 0, v_fileName_5216_);
    crate::leanh::lean_ctor_set(v___x_5233_, 1, v_fileMap_5217_);
    crate::leanh::lean_ctor_set(v___x_5233_, 2, v_options_5218_);
    crate::leanh::lean_ctor_set(v___x_5233_, 3, v_currRecDepth_5219_);
    crate::leanh::lean_ctor_set(v___x_5233_, 4, v_maxRecDepth_5220_);
    crate::leanh::lean_ctor_set(v___x_5233_, 5, v_ref_5232_);
    crate::leanh::lean_ctor_set(v___x_5233_, 6, v_currNamespace_5222_);
    crate::leanh::lean_ctor_set(v___x_5233_, 7, v_openDecls_5223_);
    crate::leanh::lean_ctor_set(v___x_5233_, 8, v_initHeartbeats_5224_);
    crate::leanh::lean_ctor_set(v___x_5233_, 9, v_maxHeartbeats_5225_);
    crate::leanh::lean_ctor_set(v___x_5233_, 10, v_quotContext_5226_);
    crate::leanh::lean_ctor_set(v___x_5233_, 11, v_currMacroScope_5227_);
    crate::leanh::lean_ctor_set(v___x_5233_, 12, v_cancelTk_x3f_5229_);
    crate::leanh::lean_ctor_set(v___x_5233_, 13, v_inheritedTraceOptions_5231_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5233_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5228_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5233_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5230_,
    );
    v___x_5234_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_5212_, v___x_5233_, v___y_5214_);
    crate::leanh::lean_dec_ref_known(v___x_5233_, 14);
    return v___x_5234_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg___boxed(
    mut v_ref_5235_: *mut crate::leanh::LeanObject,
    mut v_msg_5236_: *mut crate::leanh::LeanObject,
    mut v___y_5237_: *mut crate::leanh::LeanObject,
    mut v___y_5238_: *mut crate::leanh::LeanObject,
    mut v___y_5239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5240_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(
            v_ref_5235_,
            v_msg_5236_,
            v___y_5237_,
            v___y_5238_,
        );
    crate::leanh::lean_dec(v___y_5238_);
    crate::leanh::lean_dec_ref(v___y_5237_);
    crate::leanh::lean_dec(v_ref_5235_);
    return v_res_5240_;
}
pub unsafe fn _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5251_ = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5;
    v___x_5252_ = l_Lean_stringToMessageData(v___x_5251_);
    return v___x_5252_;
}
pub unsafe fn _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5254_ = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7;
    v___x_5255_ = l_Lean_stringToMessageData(v___x_5254_);
    return v___x_5255_;
}
pub unsafe fn l_Lean_Meta_Attribute_Recursor_getMajorPos(
    mut v_stx_5256_: *mut crate::leanh::LeanObject,
    mut v_a_5257_: *mut crate::leanh::LeanObject,
    mut v_a_5258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: u8 = 0;
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: u8 = 0;
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_stx_5256_);
                v___x_5260_ = l_Lean_Syntax_getKind(v_stx_5256_);
                v___x_5261_ = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4;
                v___x_5262_ = lean_name_eq(v___x_5260_, v___x_5261_);
                crate::leanh::lean_dec(v___x_5260_);
                if v___x_5262_ == 0 {
                    v___x_5263_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6_once
                        ),
                        _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6,
                    );
                    v___x_5264_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_stx_5256_, v___x_5263_, v_a_5257_, v_a_5258_);
                    crate::leanh::lean_dec(v_stx_5256_);
                    return v___x_5264_;
                } else {
                    v___x_5265_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5284_ = l_Lean_Syntax_getArg(v_stx_5256_, v___x_5265_);
                    v___x_5285_ = l_Lean_Syntax_isNatLit_x3f(v___x_5284_);
                    crate::leanh::lean_dec(v___x_5284_);
                    if crate::leanh::lean_obj_tag(v___x_5285_) == 0 {
                        v___x_5286_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_5271_ = v___x_5286_;
                        state = 2;
                        continue;
                    } else {
                        v_val_5287_ = crate::leanh::lean_ctor_get(v___x_5285_, 0);
                        crate::leanh::lean_inc(v_val_5287_);
                        crate::leanh::lean_dec_ref_known(v___x_5285_, 1);
                        v___y_5271_ = v_val_5287_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5268_ = lean_nat_sub(v___y_5267_, v___x_5265_);
                crate::leanh::lean_dec(v___y_5267_);
                v___x_5269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5269_, 0, v___x_5268_);
                return v___x_5269_;
            }
            2 => {
                v___x_5272_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5273_ = lean_nat_dec_eq(v___y_5271_, v___x_5272_);
                if v___x_5273_ == 0 {
                    crate::leanh::lean_dec(v_stx_5256_);
                    v___y_5267_ = v___y_5271_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_5271_);
                    v___x_5274_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8_once
                        ),
                        _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8,
                    );
                    v___x_5275_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(v_stx_5256_, v___x_5274_, v_a_5257_, v_a_5258_);
                    crate::leanh::lean_dec(v_stx_5256_);
                    v_a_5276_ = crate::leanh::lean_ctor_get(v___x_5275_, 0);
                    v_isSharedCheck_5283_ = (!crate::leanh::lean_is_exclusive(v___x_5275_)) as u8;
                    if v_isSharedCheck_5283_ == 0 {
                        v___x_5278_ = v___x_5275_;
                        v_isShared_5279_ = v_isSharedCheck_5283_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5276_);
                        crate::leanh::lean_dec(v___x_5275_);
                        v___x_5278_ = crate::leanh::lean_box(0);
                        v_isShared_5279_ = v_isSharedCheck_5283_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5279_ == 0 {
                    v___x_5281_ = v___x_5278_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Attribute_Recursor_getMajorPos___boxed(
    mut v_stx_5288_: *mut crate::leanh::LeanObject,
    mut v_a_5289_: *mut crate::leanh::LeanObject,
    mut v_a_5290_: *mut crate::leanh::LeanObject,
    mut v_a_5291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5292_ = l_Lean_Meta_Attribute_Recursor_getMajorPos(v_stx_5288_, v_a_5289_, v_a_5290_);
    crate::leanh::lean_dec(v_a_5290_);
    crate::leanh::lean_dec_ref(v_a_5289_);
    return v_res_5292_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(
    mut v_00_u03b1_5293_: *mut crate::leanh::LeanObject,
    mut v_ref_5294_: *mut crate::leanh::LeanObject,
    mut v_msg_5295_: *mut crate::leanh::LeanObject,
    mut v___y_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5299_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___redArg(
            v_ref_5294_,
            v_msg_5295_,
            v___y_5296_,
            v___y_5297_,
        );
    return v___x_5299_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0___boxed(
    mut v_00_u03b1_5300_: *mut crate::leanh::LeanObject,
    mut v_ref_5301_: *mut crate::leanh::LeanObject,
    mut v_msg_5302_: *mut crate::leanh::LeanObject,
    mut v___y_5303_: *mut crate::leanh::LeanObject,
    mut v___y_5304_: *mut crate::leanh::LeanObject,
    mut v___y_5305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5306_ = l_Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0(
        v_00_u03b1_5300_,
        v_ref_5301_,
        v_msg_5302_,
        v___y_5303_,
        v___y_5304_,
    );
    crate::leanh::lean_dec(v___y_5304_);
    crate::leanh::lean_dec_ref(v___y_5303_);
    crate::leanh::lean_dec(v_ref_5301_);
    return v_res_5306_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(
    mut v_00_u03b1_5307_: *mut crate::leanh::LeanObject,
    mut v_msg_5308_: *mut crate::leanh::LeanObject,
    mut v___y_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5312_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___redArg(v_msg_5308_, v___y_5309_, v___y_5310_);
    return v___x_5312_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0___boxed(
    mut v_00_u03b1_5313_: *mut crate::leanh::LeanObject,
    mut v_msg_5314_: *mut crate::leanh::LeanObject,
    mut v___y_5315_: *mut crate::leanh::LeanObject,
    mut v___y_5316_: *mut crate::leanh::LeanObject,
    mut v___y_5317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5318_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_Attribute_Recursor_getMajorPos_spec__0_spec__0(v_00_u03b1_5313_, v_msg_5314_, v___y_5315_, v___y_5316_);
    crate::leanh::lean_dec(v___y_5316_);
    crate::leanh::lean_dec_ref(v___y_5315_);
    return v_res_5318_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(
    mut v_x_5319_: *mut crate::leanh::LeanObject,
    mut v_stx_5320_: *mut crate::leanh::LeanObject,
    mut v___y_5321_: *mut crate::leanh::LeanObject,
    mut v___y_5322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5324_ = l_Lean_Meta_Attribute_Recursor_getMajorPos(v_stx_5320_, v___y_5321_, v___y_5322_);
    return v___x_5324_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(
    mut v_x_5325_: *mut crate::leanh::LeanObject,
    mut v_stx_5326_: *mut crate::leanh::LeanObject,
    mut v___y_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5330_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v_x_5325_, v_stx_5326_, v___y_5327_, v___y_5328_);
    crate::leanh::lean_dec(v___y_5328_);
    crate::leanh::lean_dec_ref(v___y_5327_);
    crate::leanh::lean_dec(v_x_5325_);
    return v_res_5330_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: u64 = 0;
    v___x_5337_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
    v___x_5338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5337_);
    return v___x_5338_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5339_: u64 = 0;
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5339_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
    v___x_5340_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
    v___x_5341_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_5341_, 0, v___x_5340_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_5341_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5339_,
    );
    return v___x_5341_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5342_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5342_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5343_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
    v___x_5344_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5344_, 0, v___x_5343_);
    return v___x_5344_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5345_ = crate::leanh::lean_box(1);
    v___x_5346_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_5347_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
    v___x_5348_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5348_, 0, v___x_5347_);
    crate::leanh::lean_ctor_set(v___x_5348_, 1, v___x_5346_);
    crate::leanh::lean_ctor_set(v___x_5348_, 2, v___x_5345_);
    return v___x_5348_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5351_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
    v___x_5352_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5353_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5353_, 0, v___x_5352_);
    crate::leanh::lean_ctor_set(v___x_5353_, 1, v___x_5352_);
    crate::leanh::lean_ctor_set(v___x_5353_, 2, v___x_5352_);
    crate::leanh::lean_ctor_set(v___x_5353_, 3, v___x_5352_);
    crate::leanh::lean_ctor_set(v___x_5353_, 4, v___x_5351_);
    crate::leanh::lean_ctor_set(v___x_5353_, 5, v___x_5351_);
    crate::leanh::lean_ctor_set(v___x_5353_, 6, v___x_5351_);
    crate::leanh::lean_ctor_set(v___x_5353_, 7, v___x_5351_);
    crate::leanh::lean_ctor_set(v___x_5353_, 8, v___x_5351_);
    crate::leanh::lean_ctor_set(v___x_5353_, 9, v___x_5351_);
    return v___x_5353_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5354_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
    v___x_5355_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5355_, 0, v___x_5354_);
    crate::leanh::lean_ctor_set(v___x_5355_, 1, v___x_5354_);
    crate::leanh::lean_ctor_set(v___x_5355_, 2, v___x_5354_);
    crate::leanh::lean_ctor_set(v___x_5355_, 3, v___x_5354_);
    crate::leanh::lean_ctor_set(v___x_5355_, 4, v___x_5354_);
    crate::leanh::lean_ctor_set(v___x_5355_, 5, v___x_5354_);
    return v___x_5355_;
}
pub unsafe fn _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5356_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
    v___x_5357_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5357_, 0, v___x_5356_);
    crate::leanh::lean_ctor_set(v___x_5357_, 1, v___x_5356_);
    crate::leanh::lean_ctor_set(v___x_5357_, 2, v___x_5356_);
    crate::leanh::lean_ctor_set(v___x_5357_, 3, v___x_5356_);
    crate::leanh::lean_ctor_set(v___x_5357_, 4, v___x_5356_);
    return v___x_5357_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(
    mut v___x_5358_: *mut crate::leanh::LeanObject,
    mut v_declName_5359_: *mut crate::leanh::LeanObject,
    mut v_majorPos_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5364_: u8 = 0;
    let mut v___x_5365_: u8 = 0;
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5383_: u8 = 0;
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5388_: u8 = 0;
    let mut v_unused_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5392_: u8 = 0;
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5396_: u8 = 0;
    let mut v_unused_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5401_: u8 = 0;
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5364_ = 0;
                v___x_5365_ = 1;
                v___x_5366_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
                v___x_5367_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5368_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
                v___x_5369_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
                v___x_5370_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
                v___x_5371_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_5358_);
                v___x_5372_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_5372_, 0, v___x_5366_);
                crate::leanh::lean_ctor_set(v___x_5372_, 1, v___x_5358_);
                crate::leanh::lean_ctor_set(v___x_5372_, 2, v___x_5369_);
                crate::leanh::lean_ctor_set(v___x_5372_, 3, v___x_5370_);
                crate::leanh::lean_ctor_set(v___x_5372_, 4, v___x_5371_);
                crate::leanh::lean_ctor_set(v___x_5372_, 5, v___x_5367_);
                crate::leanh::lean_ctor_set(v___x_5372_, 6, v___x_5371_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5372_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_5364_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5372_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_5364_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5372_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_5364_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5372_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_5365_,
                );
                v___x_5373_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__7_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
                v___x_5374_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__8_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
                v___x_5375_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_);
                v___x_5376_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5376_, 0, v___x_5373_);
                crate::leanh::lean_ctor_set(v___x_5376_, 1, v___x_5374_);
                crate::leanh::lean_ctor_set(v___x_5376_, 2, v___x_5358_);
                crate::leanh::lean_ctor_set(v___x_5376_, 3, v___x_5368_);
                crate::leanh::lean_ctor_set(v___x_5376_, 4, v___x_5375_);
                v___x_5377_ = lean_st_mk_ref(v___x_5376_);
                v___x_5378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5378_, 0, v_majorPos_5360_);
                v___x_5379_ = crate::leanh::lean_box(0);
                v___x_5380_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(
                    v_declName_5359_,
                    v___x_5378_,
                    v___x_5372_,
                    v___x_5377_,
                    v___y_5361_,
                    v___y_5362_,
                );
                crate::leanh::lean_dec_ref_known(v___x_5372_, 7);
                if crate::leanh::lean_obj_tag(v___x_5380_) == 0 {
                    v_isSharedCheck_5388_ = (!crate::leanh::lean_is_exclusive(v___x_5380_)) as u8;
                    if v_isSharedCheck_5388_ == 0 {
                        v_unused_5389_ = crate::leanh::lean_ctor_get(v___x_5380_, 0);
                        crate::leanh::lean_dec(v_unused_5389_);
                        v___x_5382_ = v___x_5380_;
                        v_isShared_5383_ = v_isSharedCheck_5388_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5380_);
                        v___x_5382_ = crate::leanh::lean_box(0);
                        v_isShared_5383_ = v_isSharedCheck_5388_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5377_);
                    if crate::leanh::lean_obj_tag(v___x_5380_) == 0 {
                        v_isSharedCheck_5396_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5380_)) as u8;
                        if v_isSharedCheck_5396_ == 0 {
                            v_unused_5397_ = crate::leanh::lean_ctor_get(v___x_5380_, 0);
                            crate::leanh::lean_dec(v_unused_5397_);
                            v___x_5391_ = v___x_5380_;
                            v_isShared_5392_ = v_isSharedCheck_5396_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5380_);
                            v___x_5391_ = crate::leanh::lean_box(0);
                            v_isShared_5392_ = v_isSharedCheck_5396_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5398_ = crate::leanh::lean_ctor_get(v___x_5380_, 0);
                        v_isSharedCheck_5405_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5380_)) as u8;
                        if v_isSharedCheck_5405_ == 0 {
                            v___x_5400_ = v___x_5380_;
                            v_isShared_5401_ = v_isSharedCheck_5405_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5398_);
                            crate::leanh::lean_dec(v___x_5380_);
                            v___x_5400_ = crate::leanh::lean_box(0);
                            v_isShared_5401_ = v_isSharedCheck_5405_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5384_ = lean_st_ref_get(v___x_5377_);
                crate::leanh::lean_dec(v___x_5377_);
                crate::leanh::lean_dec(v___x_5384_);
                if v_isShared_5383_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5382_, 0, v___x_5379_);
                    v___x_5386_ = v___x_5382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5387_, 0, v___x_5379_);
                    v___x_5386_ = v_reuseFailAlloc_5387_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5386_;
            }
            3 => {
                if v_isShared_5392_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5391_, 0);
                    crate::leanh::lean_ctor_set(v___x_5391_, 0, v___x_5379_);
                    v___x_5394_ = v___x_5391_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5395_, 0, v___x_5379_);
                    v___x_5394_ = v_reuseFailAlloc_5395_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5394_;
            }
            5 => {
                if v_isShared_5401_ == 0 {
                    v___x_5403_ = v___x_5400_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_a_5398_);
                    v___x_5403_ = v_reuseFailAlloc_5404_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(
    mut v___x_5406_: *mut crate::leanh::LeanObject,
    mut v_declName_5407_: *mut crate::leanh::LeanObject,
    mut v_majorPos_5408_: *mut crate::leanh::LeanObject,
    mut v___y_5409_: *mut crate::leanh::LeanObject,
    mut v___y_5410_: *mut crate::leanh::LeanObject,
    mut v___y_5411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5412_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v___x_5406_, v_declName_5407_, v_majorPos_5408_, v___y_5409_, v___y_5410_);
    crate::leanh::lean_dec(v___y_5410_);
    crate::leanh::lean_dec_ref(v___y_5409_);
    return v_res_5412_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(
    mut v___x_5413_: u8,
    mut v_env_5414_: *mut crate::leanh::LeanObject,
    mut v_n_5415_: *mut crate::leanh::LeanObject,
    mut v_x_5416_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5417_: u8 = 0;
    v___x_5417_ = l_Lean_Environment_contains(v_env_5414_, v_n_5415_, v___x_5413_);
    return v___x_5417_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(
    mut v___x_5418_: *mut crate::leanh::LeanObject,
    mut v_env_5419_: *mut crate::leanh::LeanObject,
    mut v_n_5420_: *mut crate::leanh::LeanObject,
    mut v_x_5421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643__boxed_5422_: u8 = 0;
    let mut v_res_5423_: u8 = 0;
    let mut v_r_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643__boxed_5422_ = (crate::leanh::lean_unbox(v___x_5418_) as u8);
    v_res_5423_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_(v___x_643__boxed_5422_, v_env_5419_, v_n_5420_, v_x_5421_);
    crate::leanh::lean_dec(v_x_5421_);
    v_r_5424_ = crate::leanh::lean_box((v_res_5423_) as usize);
    return v_r_5424_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5452_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_;
    v___x_5453_ = l_Lean_registerParametricAttribute___redArg(v___x_5452_);
    return v___x_5453_;
}
pub unsafe fn l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2____boxed(
    mut v_a_5454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5455_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_();
    return v_res_5455_;
}
pub unsafe fn l_Lean_Meta_getMajorPos_x3f(
    mut v_env_5456_: *mut crate::leanh::LeanObject,
    mut v_declName_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5458_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5459_ = l_Lean_Meta_recursorAttribute;
    v___x_5460_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_5458_,
        v___x_5459_,
        v_env_5456_,
        v_declName_5457_,
    );
    return v___x_5460_;
}
pub unsafe fn l_Lean_Meta_mkRecursorInfo(
    mut v_declName_5461_: *mut crate::leanh::LeanObject,
    mut v_majorPos_x3f_5462_: *mut crate::leanh::LeanObject,
    mut v_a_5463_: *mut crate::leanh::LeanObject,
    mut v_a_5464_: *mut crate::leanh::LeanObject,
    mut v_a_5465_: *mut crate::leanh::LeanObject,
    mut v_a_5466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5468_ = lean_st_ref_get(v_a_5466_);
    if crate::leanh::lean_obj_tag(v_majorPos_x3f_5462_) == 0 {
        let mut v_env_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_env_5469_ = crate::leanh::lean_ctor_get(v___x_5468_, 0);
        crate::leanh::lean_inc_ref(v_env_5469_);
        crate::leanh::lean_dec(v___x_5468_);
        crate::leanh::lean_inc(v_declName_5461_);
        v___x_5470_ = l_Lean_Meta_getMajorPos_x3f(v_env_5469_, v_declName_5461_);
        v___x_5471_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(
            v_declName_5461_,
            v___x_5470_,
            v_a_5463_,
            v_a_5464_,
            v_a_5465_,
            v_a_5466_,
        );
        return v___x_5471_;
    } else {
        let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_5468_);
        v___x_5472_ = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(
            v_declName_5461_,
            v_majorPos_x3f_5462_,
            v_a_5463_,
            v_a_5464_,
            v_a_5465_,
            v_a_5466_,
        );
        return v___x_5472_;
    }
}
pub unsafe fn l_Lean_Meta_mkRecursorInfo___boxed(
    mut v_declName_5473_: *mut crate::leanh::LeanObject,
    mut v_majorPos_x3f_5474_: *mut crate::leanh::LeanObject,
    mut v_a_5475_: *mut crate::leanh::LeanObject,
    mut v_a_5476_: *mut crate::leanh::LeanObject,
    mut v_a_5477_: *mut crate::leanh::LeanObject,
    mut v_a_5478_: *mut crate::leanh::LeanObject,
    mut v_a_5479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5480_ = l_Lean_Meta_mkRecursorInfo(
        v_declName_5473_,
        v_majorPos_x3f_5474_,
        v_a_5475_,
        v_a_5476_,
        v_a_5477_,
        v_a_5478_,
    );
    crate::leanh::lean_dec(v_a_5478_);
    crate::leanh::lean_dec_ref(v_a_5477_);
    crate::leanh::lean_dec(v_a_5476_);
    crate::leanh::lean_dec_ref(v_a_5475_);
    return v_res_5480_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_RecursorInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecursorInfo_3248140585____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_recursorAttribute = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_recursorAttribute);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_RecursorInfo(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_RecursorInfo(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_RecursorInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_RecursorInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_RecursorInfo(builtin);
}
