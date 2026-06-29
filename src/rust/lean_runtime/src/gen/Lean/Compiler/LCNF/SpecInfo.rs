// Lean compiler output
// Module: Lean.Compiler.LCNF.SpecInfo
// Imports: Lean.Compiler.LCNF.FixedParams Lean.Compiler.LCNF.InferType
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Data::Array::BinSearch::l_Array_binSearchAux___redArg;
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::List::Basic::{l_List_mapTR_loop___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_id___boxed, l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::l_Lean_Compiler_LCNF_instInhabitedParam_default;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::l_Lean_Compiler_LCNF_getPurity___redArg;
use crate::r#gen::Lean::Compiler::LCNF::FixedParams::{
    initialize_Lean_Compiler_LCNF_FixedParams, l_Lean_Compiler_LCNF_mkFixedParamsMap,
    runtime_initialize_Lean_Compiler_LCNF_FixedParams,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    initialize_Lean_Compiler_LCNF_InferType, runtime_initialize_Lean_Compiler_LCNF_InferType,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg, l_Lean_Compiler_LCNF_isTypeFormerType,
};
use crate::r#gen::Lean::Compiler::Specialize::{
    l_Lean_Compiler_getSpecializationArgs_x3f, l_Lean_Compiler_hasNospecializeAttribute,
    l_Lean_Compiler_hasWeakSpecializeAttribute,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_quickLt;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_containsFVar, l_Lean_Expr_getAppFn};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
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
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        112, 101, 99, 80, 97, 114, 97, 109, 73, 110, 102, 111, 46, 102, 105, 120, 101, 100, 72, 79,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        112, 101, 99, 80, 97, 114, 97, 109, 73, 110, 102, 111, 46, 102, 105, 120, 101, 100, 78,
        101, 117, 116, 114, 97, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4_value:
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
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        112, 101, 99, 80, 97, 114, 97, 109, 73, 110, 102, 111, 46, 117, 115, 101, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        112, 101, 99, 80, 97, 114, 97, 109, 73, 110, 102, 111, 46, 111, 116, 104, 101, 114, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        112, 101, 99, 80, 97, 114, 97, 109, 73, 110, 102, 111, 46, 102, 105, 120, 101, 100, 73,
        110, 115, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0_value:
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
    m_data: [73, 0],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3_value:
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
    m_data: [87, 0],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6_value:
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
    m_data: [72, 0],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9_value:
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
    m_data: [78, 0],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12_value:
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
    m_data: [85, 0],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15_value:
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
    m_data: [79, 0],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecEntry: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0_value:
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
        44, 32, 97, 108, 114, 101, 97, 100, 121, 83, 112, 101, 99, 105, 97, 108, 105, 122, 101,
        100, 63, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2_value:
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
    m_data: [44, 32, 105, 110, 102, 111, 58, 32, 0],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4_value:
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
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5_value:
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
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_id___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 112, 101, 99, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8543197020067251012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13270991020494245093 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2852275733072608516 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_SpecState_addEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<4> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_specExtension: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 112, 101, 99, 73, 110, 102, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 99, 111, 109, 112, 117, 116, 101, 83, 112, 101, 99, 69, 110, 116, 114, 105, 101, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_computeSpecEntries___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_computeSpecEntries___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_computeSpecEntries___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4_value:
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
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5_value:
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
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 102, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value) as *mut crate::leanh::LeanObject,3434285012924019335 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value) as *mut crate::leanh::LeanObject,13745773733782817519 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_saveSpecEntries___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_saveSpecEntries___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_saveSpecEntries___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 112, 101, 99, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9426862755842527165 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3947991056360201544 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2285067212717554721 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13153666271249394511 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17406323380265421602 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11322028819074094999 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16051372844745760850 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9403487116094859347 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2146848419678310453 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5968087063485750496 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,463555809555801384 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 513551779 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,4443312571263244686 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4667400838671785689 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12002315305368908305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5269381400095652076 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx(
    mut v_x_2131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2131_) {
        0 => {
            let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2132_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2132_;
        }
        1 => {
            let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2133_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2133_;
        }
        2 => {
            let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2134_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2134_;
        }
        3 => {
            let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2135_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2135_;
        }
        _ => {
            let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2136_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2136_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx___boxed(
    mut v_x_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2138_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx(v_x_2137_);
    crate::leanh::lean_dec(v_x_2137_);
    return v_res_2138_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(
    mut v_t_2139_: *mut crate::leanh::LeanObject,
    mut v_k_2140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2139_) == 0 {
        let mut v_weak_2141_: u8 = 0;
        let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_weak_2141_ = crate::leanh::lean_ctor_get_uint8(v_t_2139_, 0 as u32);
        v___x_2142_ = crate::leanh::lean_box((v_weak_2141_) as usize);
        v___x_2143_ = crate::leanh::lean_apply_1(v_k_2140_, v___x_2142_);
        return v___x_2143_;
    } else {
        return v_k_2140_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg___boxed(
    mut v_t_2144_: *mut crate::leanh::LeanObject,
    mut v_k_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2146_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2144_, v_k_2145_);
    crate::leanh::lean_dec(v_t_2144_);
    return v_res_2146_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim(
    mut v_motive_2147_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2148_: *mut crate::leanh::LeanObject,
    mut v_t_2149_: *mut crate::leanh::LeanObject,
    mut v_h_2150_: *mut crate::leanh::LeanObject,
    mut v_k_2151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2152_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2149_, v_k_2151_);
    return v___x_2152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___boxed(
    mut v_motive_2153_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2154_: *mut crate::leanh::LeanObject,
    mut v_t_2155_: *mut crate::leanh::LeanObject,
    mut v_h_2156_: *mut crate::leanh::LeanObject,
    mut v_k_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim(
        v_motive_2153_,
        v_ctorIdx_2154_,
        v_t_2155_,
        v_h_2156_,
        v_k_2157_,
    );
    crate::leanh::lean_dec(v_t_2155_);
    crate::leanh::lean_dec(v_ctorIdx_2154_);
    return v_res_2158_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg(
    mut v_t_2159_: *mut crate::leanh::LeanObject,
    mut v_fixedInst_2160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2159_, v_fixedInst_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg___boxed(
    mut v_t_2162_: *mut crate::leanh::LeanObject,
    mut v_fixedInst_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2164_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg(v_t_2162_, v_fixedInst_2163_);
    crate::leanh::lean_dec(v_t_2162_);
    return v_res_2164_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim(
    mut v_motive_2165_: *mut crate::leanh::LeanObject,
    mut v_t_2166_: *mut crate::leanh::LeanObject,
    mut v_h_2167_: *mut crate::leanh::LeanObject,
    mut v_fixedInst_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2169_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2166_, v_fixedInst_2168_);
    return v___x_2169_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___boxed(
    mut v_motive_2170_: *mut crate::leanh::LeanObject,
    mut v_t_2171_: *mut crate::leanh::LeanObject,
    mut v_h_2172_: *mut crate::leanh::LeanObject,
    mut v_fixedInst_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim(
        v_motive_2170_,
        v_t_2171_,
        v_h_2172_,
        v_fixedInst_2173_,
    );
    crate::leanh::lean_dec(v_t_2171_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg(
    mut v_t_2175_: *mut crate::leanh::LeanObject,
    mut v_fixedHO_2176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2175_, v_fixedHO_2176_);
    return v___x_2177_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg___boxed(
    mut v_t_2178_: *mut crate::leanh::LeanObject,
    mut v_fixedHO_2179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2180_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg(v_t_2178_, v_fixedHO_2179_);
    crate::leanh::lean_dec(v_t_2178_);
    return v_res_2180_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim(
    mut v_motive_2181_: *mut crate::leanh::LeanObject,
    mut v_t_2182_: *mut crate::leanh::LeanObject,
    mut v_h_2183_: *mut crate::leanh::LeanObject,
    mut v_fixedHO_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2185_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2182_, v_fixedHO_2184_);
    return v___x_2185_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___boxed(
    mut v_motive_2186_: *mut crate::leanh::LeanObject,
    mut v_t_2187_: *mut crate::leanh::LeanObject,
    mut v_h_2188_: *mut crate::leanh::LeanObject,
    mut v_fixedHO_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2190_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim(
        v_motive_2186_,
        v_t_2187_,
        v_h_2188_,
        v_fixedHO_2189_,
    );
    crate::leanh::lean_dec(v_t_2187_);
    return v_res_2190_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg(
    mut v_t_2191_: *mut crate::leanh::LeanObject,
    mut v_fixedNeutral_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2193_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2191_, v_fixedNeutral_2192_);
    return v___x_2193_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg___boxed(
    mut v_t_2194_: *mut crate::leanh::LeanObject,
    mut v_fixedNeutral_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2196_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg(
        v_t_2194_,
        v_fixedNeutral_2195_,
    );
    crate::leanh::lean_dec(v_t_2194_);
    return v_res_2196_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim(
    mut v_motive_2197_: *mut crate::leanh::LeanObject,
    mut v_t_2198_: *mut crate::leanh::LeanObject,
    mut v_h_2199_: *mut crate::leanh::LeanObject,
    mut v_fixedNeutral_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2201_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2198_, v_fixedNeutral_2200_);
    return v___x_2201_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___boxed(
    mut v_motive_2202_: *mut crate::leanh::LeanObject,
    mut v_t_2203_: *mut crate::leanh::LeanObject,
    mut v_h_2204_: *mut crate::leanh::LeanObject,
    mut v_fixedNeutral_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim(
        v_motive_2202_,
        v_t_2203_,
        v_h_2204_,
        v_fixedNeutral_2205_,
    );
    crate::leanh::lean_dec(v_t_2203_);
    return v_res_2206_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg(
    mut v_t_2207_: *mut crate::leanh::LeanObject,
    mut v_user_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2209_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2207_, v_user_2208_);
    return v___x_2209_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg___boxed(
    mut v_t_2210_: *mut crate::leanh::LeanObject,
    mut v_user_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2212_ = l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg(v_t_2210_, v_user_2211_);
    crate::leanh::lean_dec(v_t_2210_);
    return v_res_2212_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_user_elim(
    mut v_motive_2213_: *mut crate::leanh::LeanObject,
    mut v_t_2214_: *mut crate::leanh::LeanObject,
    mut v_h_2215_: *mut crate::leanh::LeanObject,
    mut v_user_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2214_, v_user_2216_);
    return v___x_2217_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___boxed(
    mut v_motive_2218_: *mut crate::leanh::LeanObject,
    mut v_t_2219_: *mut crate::leanh::LeanObject,
    mut v_h_2220_: *mut crate::leanh::LeanObject,
    mut v_user_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2222_ = l_Lean_Compiler_LCNF_SpecParamInfo_user_elim(
        v_motive_2218_,
        v_t_2219_,
        v_h_2220_,
        v_user_2221_,
    );
    crate::leanh::lean_dec(v_t_2219_);
    return v_res_2222_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg(
    mut v_t_2223_: *mut crate::leanh::LeanObject,
    mut v_other_2224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2225_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2223_, v_other_2224_);
    return v___x_2225_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg___boxed(
    mut v_t_2226_: *mut crate::leanh::LeanObject,
    mut v_other_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg(v_t_2226_, v_other_2227_);
    crate::leanh::lean_dec(v_t_2226_);
    return v_res_2228_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_other_elim(
    mut v_motive_2229_: *mut crate::leanh::LeanObject,
    mut v_t_2230_: *mut crate::leanh::LeanObject,
    mut v_h_2231_: *mut crate::leanh::LeanObject,
    mut v_other_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2233_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2230_, v_other_2232_);
    return v___x_2233_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___boxed(
    mut v_motive_2234_: *mut crate::leanh::LeanObject,
    mut v_t_2235_: *mut crate::leanh::LeanObject,
    mut v_h_2236_: *mut crate::leanh::LeanObject,
    mut v_other_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2238_ = l_Lean_Compiler_LCNF_SpecParamInfo_other_elim(
        v_motive_2234_,
        v_t_2235_,
        v_h_2236_,
        v_other_2237_,
    );
    crate::leanh::lean_dec(v_t_2235_);
    return v_res_2238_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2261_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2262_ = lean_nat_to_int(v___x_2261_);
    return v___x_2262_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2264_ = lean_nat_to_int(v___x_2263_);
    return v___x_2264_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr(
    mut v_x_2265_: *mut crate::leanh::LeanObject,
    mut v_prec_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: u8 = 0;
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weak_2295_: u8 = 0;
    let mut v___y_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u8 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_x_2265_) {
                    0 => {
                        v_weak_2295_ = crate::leanh::lean_ctor_get_uint8(v_x_2265_, 0 as u32);
                        v___x_2305_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_2306_ = lean_nat_dec_le(v___x_2305_, v_prec_2266_);
                        if v___x_2306_ == 0 {
                            v___x_2307_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2297_ = v___x_2307_;
                            state = 5;
                            continue;
                        } else {
                            v___x_2308_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2297_ = v___x_2308_;
                            state = 5;
                            continue;
                        }
                    }
                    1 => {
                        v___x_2309_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_2310_ = lean_nat_dec_le(v___x_2309_, v_prec_2266_);
                        if v___x_2310_ == 0 {
                            v___x_2311_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2268_ = v___x_2311_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2312_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2268_ = v___x_2312_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v___x_2313_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_2314_ = lean_nat_dec_le(v___x_2313_, v_prec_2266_);
                        if v___x_2314_ == 0 {
                            v___x_2315_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2275_ = v___x_2315_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2316_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2275_ = v___x_2316_;
                            state = 2;
                            continue;
                        }
                    }
                    3 => {
                        v___x_2317_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_2318_ = lean_nat_dec_le(v___x_2317_, v_prec_2266_);
                        if v___x_2318_ == 0 {
                            v___x_2319_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2282_ = v___x_2319_;
                            state = 3;
                            continue;
                        } else {
                            v___x_2320_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2282_ = v___x_2320_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2321_ = crate::leanh::lean_unsigned_to_nat(1024);
                        v___x_2322_ = lean_nat_dec_le(v___x_2321_, v_prec_2266_);
                        if v___x_2322_ == 0 {
                            v___x_2323_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2289_ = v___x_2323_;
                            state = 4;
                            continue;
                        } else {
                            v___x_2324_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2289_ = v___x_2324_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2269_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1;
                crate::leanh::lean_inc(v___y_2268_);
                v___x_2270_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2270_, 0, v___y_2268_);
                crate::leanh::lean_ctor_set(v___x_2270_, 1, v___x_2269_);
                v___x_2271_ = 0;
                v___x_2272_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2272_, 0, v___x_2270_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2272_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2271_,
                );
                v___x_2273_ = l_Repr_addAppParen(v___x_2272_, v_prec_2266_);
                return v___x_2273_;
            }
            2 => {
                v___x_2276_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3;
                crate::leanh::lean_inc(v___y_2275_);
                v___x_2277_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2277_, 0, v___y_2275_);
                crate::leanh::lean_ctor_set(v___x_2277_, 1, v___x_2276_);
                v___x_2278_ = 0;
                v___x_2279_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2279_, 0, v___x_2277_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2279_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2278_,
                );
                v___x_2280_ = l_Repr_addAppParen(v___x_2279_, v_prec_2266_);
                return v___x_2280_;
            }
            3 => {
                v___x_2283_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5;
                crate::leanh::lean_inc(v___y_2282_);
                v___x_2284_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2284_, 0, v___y_2282_);
                crate::leanh::lean_ctor_set(v___x_2284_, 1, v___x_2283_);
                v___x_2285_ = 0;
                v___x_2286_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2286_, 0, v___x_2284_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2286_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2285_,
                );
                v___x_2287_ = l_Repr_addAppParen(v___x_2286_, v_prec_2266_);
                return v___x_2287_;
            }
            4 => {
                v___x_2290_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7;
                crate::leanh::lean_inc(v___y_2289_);
                v___x_2291_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2291_, 0, v___y_2289_);
                crate::leanh::lean_ctor_set(v___x_2291_, 1, v___x_2290_);
                v___x_2292_ = 0;
                v___x_2293_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2293_, 0, v___x_2291_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2293_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2292_,
                );
                v___x_2294_ = l_Repr_addAppParen(v___x_2293_, v_prec_2266_);
                return v___x_2294_;
            }
            5 => {
                v___x_2298_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10;
                v___x_2299_ = l_Bool_repr___redArg(v_weak_2295_);
                v___x_2300_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2300_, 0, v___x_2298_);
                crate::leanh::lean_ctor_set(v___x_2300_, 1, v___x_2299_);
                crate::leanh::lean_inc(v___y_2297_);
                v___x_2301_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2301_, 0, v___y_2297_);
                crate::leanh::lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                v___x_2302_ = 0;
                v___x_2303_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2303_, 0, v___x_2301_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2303_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2302_,
                );
                v___x_2304_ = l_Repr_addAppParen(v___x_2303_, v_prec_2266_);
                return v___x_2304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___boxed(
    mut v_x_2325_: *mut crate::leanh::LeanObject,
    mut v_prec_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2327_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr(v_x_2325_, v_prec_2326_);
    crate::leanh::lean_dec(v_prec_2326_);
    crate::leanh::lean_dec(v_x_2325_);
    return v_res_2327_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(
    mut v_x_2330_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_2330_) {
        0 => {
            let mut v_weak_2331_: u8 = 0;
            v_weak_2331_ = crate::leanh::lean_ctor_get_uint8(v_x_2330_, 0 as u32);
            if v_weak_2331_ == 0 {
                let mut v___x_2332_: u8 = 0;
                v___x_2332_ = 1;
                return v___x_2332_;
            } else {
                let mut v___x_2333_: u8 = 0;
                v___x_2333_ = 0;
                return v___x_2333_;
            }
        }
        2 => {
            let mut v___x_2334_: u8 = 0;
            v___x_2334_ = 0;
            return v___x_2334_;
        }
        4 => {
            let mut v___x_2335_: u8 = 0;
            v___x_2335_ = 0;
            return v___x_2335_;
        }
        _ => {
            let mut v___x_2336_: u8 = 0;
            v___x_2336_ = 1;
            return v___x_2336_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization___boxed(
    mut v_x_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2338_: u8 = 0;
    let mut v_r_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(v_x_2337_);
    crate::leanh::lean_dec(v_x_2337_);
    v_r_2339_ = crate::leanh::lean_box((v_res_2338_) as usize);
    return v_r_2339_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2343_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1;
    v___x_2344_ = l_Lean_MessageData_ofFormat(v___x_2343_);
    return v___x_2344_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4;
    v___x_2349_ = l_Lean_MessageData_ofFormat(v___x_2348_);
    return v___x_2349_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7;
    v___x_2354_ = l_Lean_MessageData_ofFormat(v___x_2353_);
    return v___x_2354_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10;
    v___x_2359_ = l_Lean_MessageData_ofFormat(v___x_2358_);
    return v___x_2359_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2363_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13;
    v___x_2364_ = l_Lean_MessageData_ofFormat(v___x_2363_);
    return v___x_2364_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2368_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16;
    v___x_2369_ = l_Lean_MessageData_ofFormat(v___x_2368_);
    return v___x_2369_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0(
    mut v_x_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2370_) {
        0 => {
            let mut v_weak_2371_: u8 = 0;
            v_weak_2371_ = crate::leanh::lean_ctor_get_uint8(v_x_2370_, 0 as u32);
            if v_weak_2371_ == 0 {
                let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2372_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
                return v___x_2372_;
            } else {
                let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2373_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
                return v___x_2373_;
            }
        }
        1 => {
            let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2374_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once
                ),
                _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8,
            );
            return v___x_2374_;
        }
        2 => {
            let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2375_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once
                ),
                _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11,
            );
            return v___x_2375_;
        }
        3 => {
            let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2376_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once
                ),
                _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14,
            );
            return v___x_2376_;
        }
        _ => {
            let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2377_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once
                ),
                _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17,
            );
            return v___x_2377_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___boxed(
    mut v_x_2378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2379_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0(v_x_2378_);
    crate::leanh::lean_dec(v_x_2378_);
    return v_res_2379_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2391_ = l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0;
    v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2;
    v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
    return v___x_2395_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1(
    mut v___f_2398_: *mut crate::leanh::LeanObject,
    mut v_x_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsInfo_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alreadySpecialized_2402_: u8 = 0;
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_2400_ = crate::leanh::lean_ctor_get(v_x_2399_, 0);
                crate::leanh::lean_inc(v_declName_2400_);
                v_paramsInfo_2401_ = crate::leanh::lean_ctor_get(v_x_2399_, 1);
                crate::leanh::lean_inc_ref(v_paramsInfo_2401_);
                v_alreadySpecialized_2402_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2399_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                crate::leanh::lean_dec_ref(v_x_2399_);
                v___x_2403_ = l_Lean_MessageData_ofName(v_declName_2400_);
                v___x_2404_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1,
                );
                v___x_2405_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2403_);
                crate::leanh::lean_ctor_set(v___x_2405_, 1, v___x_2404_);
                if v_alreadySpecialized_2402_ == 0 {
                    v___x_2418_ =
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4;
                    v___y_2407_ = v___x_2418_;
                    state = 1;
                    continue;
                } else {
                    v___x_2419_ =
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5;
                    v___y_2407_ = v___x_2419_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2407_);
                v___x_2408_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2408_, 0, v___y_2407_);
                v___x_2409_ = l_Lean_MessageData_ofFormat(v___x_2408_);
                v___x_2410_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2410_, 0, v___x_2405_);
                crate::leanh::lean_ctor_set(v___x_2410_, 1, v___x_2409_);
                v___x_2411_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3,
                );
                v___x_2412_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2412_, 0, v___x_2410_);
                crate::leanh::lean_ctor_set(v___x_2412_, 1, v___x_2411_);
                v___x_2413_ = lean_array_to_list(v_paramsInfo_2401_);
                v___x_2414_ = crate::leanh::lean_box(0);
                v___x_2415_ = l_List_mapTR_loop___redArg(v___f_2398_, v___x_2413_, v___x_2414_);
                v___x_2416_ = l_Lean_MessageData_ofList(v___x_2415_);
                v___x_2417_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2412_);
                crate::leanh::lean_ctor_set(v___x_2417_, 1, v___x_2416_);
                return v___x_2417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2423_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0,
    );
    v___x_2425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
    return v___x_2425_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1,
    );
    return v___x_2426_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSpecState() -> *mut crate::leanh::LeanObject {
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
    return v___x_2427_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2428_: *mut crate::leanh::LeanObject,
    mut v_x_2429_: *mut crate::leanh::LeanObject,
    mut v_x_2430_: *mut crate::leanh::LeanObject,
    mut v_x_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: u8 = 0;
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2432_ = crate::leanh::lean_ctor_get(v_x_2428_, 0);
                v_vs_2433_ = crate::leanh::lean_ctor_get(v_x_2428_, 1);
                v_isSharedCheck_2457_ = (!crate::leanh::lean_is_exclusive(v_x_2428_)) as u8;
                if v_isSharedCheck_2457_ == 0 {
                    v___x_2435_ = v_x_2428_;
                    v_isShared_2436_ = v_isSharedCheck_2457_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2433_);
                    crate::leanh::lean_inc(v_ks_2432_);
                    crate::leanh::lean_dec(v_x_2428_);
                    v___x_2435_ = crate::leanh::lean_box(0);
                    v_isShared_2436_ = v_isSharedCheck_2457_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2437_ = lean_array_get_size(v_ks_2432_);
                v___x_2438_ = lean_nat_dec_lt(v_x_2429_, v___x_2437_);
                if v___x_2438_ == 0 {
                    crate::leanh::lean_dec(v_x_2429_);
                    v___x_2439_ = lean_array_push(v_ks_2432_, v_x_2430_);
                    v___x_2440_ = lean_array_push(v_vs_2433_, v_x_2431_);
                    if v_isShared_2436_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2435_, 1, v___x_2440_);
                        crate::leanh::lean_ctor_set(v___x_2435_, 0, v___x_2439_);
                        v___x_2442_ = v___x_2435_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2443_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2439_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2440_);
                        v___x_2442_ = v_reuseFailAlloc_2443_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2444_ = lean_array_fget_borrowed(v_ks_2432_, v_x_2429_);
                    v___x_2445_ = lean_name_eq(v_x_2430_, v_k_x27_2444_);
                    if v___x_2445_ == 0 {
                        if v_isShared_2436_ == 0 {
                            v___x_2447_ = v___x_2435_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2451_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_ks_2432_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_vs_2433_);
                            v___x_2447_ = v_reuseFailAlloc_2451_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2452_ = lean_array_fset(v_ks_2432_, v_x_2429_, v_x_2430_);
                        v___x_2453_ = lean_array_fset(v_vs_2433_, v_x_2429_, v_x_2431_);
                        crate::leanh::lean_dec(v_x_2429_);
                        if v_isShared_2436_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2435_, 1, v___x_2453_);
                            crate::leanh::lean_ctor_set(v___x_2435_, 0, v___x_2452_);
                            v___x_2455_ = v___x_2435_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2456_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2452_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 1, v___x_2453_);
                            v___x_2455_ = v_reuseFailAlloc_2456_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2442_;
            }
            3 => {
                v___x_2448_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2449_ = lean_nat_add(v_x_2429_, v___x_2448_);
                crate::leanh::lean_dec(v_x_2429_);
                v_x_2428_ = v___x_2447_;
                v_x_2429_ = v___x_2449_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(
    mut v_n_2458_: *mut crate::leanh::LeanObject,
    mut v_k_2459_: *mut crate::leanh::LeanObject,
    mut v_v_2460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2462_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2458_, v___x_2461_, v_k_2459_, v_v_2460_);
    return v___x_2462_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u64 = 0;
    v___x_2463_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_2464_ = lean_uint64_of_nat(v___x_2463_);
    return v___x_2464_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2465_: usize = 0;
    let mut v___x_2466_: usize = 0;
    let mut v___x_2467_: usize = 0;
    v___x_2465_ = 5usize;
    v___x_2466_ = 1usize;
    v___x_2467_ = lean_usize_shift_left(v___x_2466_, v___x_2465_);
    return v___x_2467_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2468_: usize = 0;
    let mut v___x_2469_: usize = 0;
    let mut v___x_2470_: usize = 0;
    v___x_2468_ = 1usize;
    v___x_2469_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0);
    v___x_2470_ = lean_usize_sub(v___x_2469_, v___x_2468_);
    return v___x_2470_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2471_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2471_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(
    mut v_x_2472_: *mut crate::leanh::LeanObject,
    mut v_x_2473_: usize,
    mut v_x_2474_: usize,
    mut v_x_2475_: *mut crate::leanh::LeanObject,
    mut v_x_2476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: usize = 0;
    let mut v___x_2480_: usize = 0;
    let mut v___x_2481_: usize = 0;
    let mut v_j_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: u8 = 0;
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v_v_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut v_node_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2512_: u8 = 0;
    let mut v___x_2513_: usize = 0;
    let mut v___x_2514_: usize = 0;
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut v_unused_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2532_: u8 = 0;
    let mut v_ks_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: usize = 0;
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: u8 = 0;
    let mut v_reuseFailAlloc_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2472_) == 0 {
                    v_es_2477_ = crate::leanh::lean_ctor_get(v_x_2472_, 0);
                    v___x_2478_ = 5usize;
                    v___x_2479_ = 1usize;
                    v___x_2480_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1);
                    v___x_2481_ = lean_usize_land(v_x_2473_, v___x_2480_);
                    v_j_2482_ = lean_usize_to_nat(v___x_2481_);
                    v___x_2483_ = lean_array_get_size(v_es_2477_);
                    v___x_2484_ = lean_nat_dec_lt(v_j_2482_, v___x_2483_);
                    if v___x_2484_ == 0 {
                        crate::leanh::lean_dec(v_j_2482_);
                        crate::leanh::lean_dec(v_x_2476_);
                        crate::leanh::lean_dec(v_x_2475_);
                        return v_x_2472_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2477_);
                        v_isSharedCheck_2521_ = (!crate::leanh::lean_is_exclusive(v_x_2472_)) as u8;
                        if v_isSharedCheck_2521_ == 0 {
                            v_unused_2522_ = crate::leanh::lean_ctor_get(v_x_2472_, 0);
                            crate::leanh::lean_dec(v_unused_2522_);
                            v___x_2486_ = v_x_2472_;
                            v_isShared_2487_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2472_);
                            v___x_2486_ = crate::leanh::lean_box(0);
                            v_isShared_2487_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2523_ = crate::leanh::lean_ctor_get(v_x_2472_, 0);
                    v_vs_2524_ = crate::leanh::lean_ctor_get(v_x_2472_, 1);
                    v_isSharedCheck_2544_ = (!crate::leanh::lean_is_exclusive(v_x_2472_)) as u8;
                    if v_isSharedCheck_2544_ == 0 {
                        v___x_2526_ = v_x_2472_;
                        v_isShared_2527_ = v_isSharedCheck_2544_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2524_);
                        crate::leanh::lean_inc(v_ks_2523_);
                        crate::leanh::lean_dec(v_x_2472_);
                        v___x_2526_ = crate::leanh::lean_box(0);
                        v_isShared_2527_ = v_isSharedCheck_2544_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2488_ = lean_array_fget(v_es_2477_, v_j_2482_);
                v___x_2489_ = crate::leanh::lean_box(0);
                v_xs_x27_2490_ = lean_array_fset(v_es_2477_, v_j_2482_, v___x_2489_);
                match crate::leanh::lean_obj_tag(v_v_2488_) {
                    0 => {
                        v_key_2497_ = crate::leanh::lean_ctor_get(v_v_2488_, 0);
                        v_val_2498_ = crate::leanh::lean_ctor_get(v_v_2488_, 1);
                        v_isSharedCheck_2508_ = (!crate::leanh::lean_is_exclusive(v_v_2488_)) as u8;
                        if v_isSharedCheck_2508_ == 0 {
                            v___x_2500_ = v_v_2488_;
                            v_isShared_2501_ = v_isSharedCheck_2508_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2498_);
                            crate::leanh::lean_inc(v_key_2497_);
                            crate::leanh::lean_dec(v_v_2488_);
                            v___x_2500_ = crate::leanh::lean_box(0);
                            v_isShared_2501_ = v_isSharedCheck_2508_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2509_ = crate::leanh::lean_ctor_get(v_v_2488_, 0);
                        v_isSharedCheck_2519_ = (!crate::leanh::lean_is_exclusive(v_v_2488_)) as u8;
                        if v_isSharedCheck_2519_ == 0 {
                            v___x_2511_ = v_v_2488_;
                            v_isShared_2512_ = v_isSharedCheck_2519_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2509_);
                            crate::leanh::lean_dec(v_v_2488_);
                            v___x_2511_ = crate::leanh::lean_box(0);
                            v_isShared_2512_ = v_isSharedCheck_2519_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2520_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2520_, 0, v_x_2475_);
                        crate::leanh::lean_ctor_set(v___x_2520_, 1, v_x_2476_);
                        v___y_2492_ = v___x_2520_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2493_ = lean_array_fset(v_xs_x27_2490_, v_j_2482_, v___y_2492_);
                crate::leanh::lean_dec(v_j_2482_);
                if v_isShared_2487_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2486_, 0, v___x_2493_);
                    v___x_2495_ = v___x_2486_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
                    v___x_2495_ = v_reuseFailAlloc_2496_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2495_;
            }
            4 => {
                v___x_2502_ = lean_name_eq(v_x_2475_, v_key_2497_);
                if v___x_2502_ == 0 {
                    crate::leanh::lean_del_object(v___x_2500_);
                    v___x_2503_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2497_,
                        v_val_2498_,
                        v_x_2475_,
                        v_x_2476_,
                    );
                    v___x_2504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2504_, 0, v___x_2503_);
                    v___y_2492_ = v___x_2504_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2498_);
                    crate::leanh::lean_dec(v_key_2497_);
                    if v_isShared_2501_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2500_, 1, v_x_2476_);
                        crate::leanh::lean_ctor_set(v___x_2500_, 0, v_x_2475_);
                        v___x_2506_ = v___x_2500_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2507_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_x_2475_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_x_2476_);
                        v___x_2506_ = v_reuseFailAlloc_2507_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2492_ = v___x_2506_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2513_ = lean_usize_shift_right(v_x_2473_, v___x_2478_);
                v___x_2514_ = lean_usize_add(v_x_2474_, v___x_2479_);
                v___x_2515_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_node_2509_, v___x_2513_, v___x_2514_, v_x_2475_, v_x_2476_);
                if v_isShared_2512_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2511_, 0, v___x_2515_);
                    v___x_2517_ = v___x_2511_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
                    v___x_2517_ = v_reuseFailAlloc_2518_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2492_ = v___x_2517_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2527_ == 0 {
                    v___x_2529_ = v___x_2526_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2543_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_ks_2523_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_vs_2524_);
                    v___x_2529_ = v_reuseFailAlloc_2543_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2530_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v___x_2529_, v_x_2475_, v_x_2476_);
                v___x_2538_ = 7usize;
                v___x_2539_ = lean_usize_dec_le(v___x_2538_, v_x_2474_);
                if v___x_2539_ == 0 {
                    v___x_2540_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2530_);
                    v___x_2541_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2542_ = lean_nat_dec_lt(v___x_2540_, v___x_2541_);
                    crate::leanh::lean_dec(v___x_2540_);
                    v___y_2532_ = v___x_2542_;
                    state = 10;
                    continue;
                } else {
                    v___y_2532_ = v___x_2539_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2532_ == 0 {
                    v_ks_2533_ = crate::leanh::lean_ctor_get(v_newNode_2530_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2533_);
                    v_vs_2534_ = crate::leanh::lean_ctor_get(v_newNode_2530_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2534_);
                    crate::leanh::lean_dec_ref(v_newNode_2530_);
                    v___x_2535_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2536_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2);
                    v___x_2537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_x_2474_, v_ks_2533_, v_vs_2534_, v___x_2535_, v___x_2536_);
                    crate::leanh::lean_dec_ref(v_vs_2534_);
                    crate::leanh::lean_dec_ref(v_ks_2533_);
                    return v___x_2537_;
                } else {
                    return v_newNode_2530_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(
    mut v_depth_2545_: usize,
    mut v_keys_2546_: *mut crate::leanh::LeanObject,
    mut v_vals_2547_: *mut crate::leanh::LeanObject,
    mut v_i_2548_: *mut crate::leanh::LeanObject,
    mut v_entries_2549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v_k_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2555_: u64 = 0;
    let mut v_h_2556_: usize = 0;
    let mut v___x_2557_: usize = 0;
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: usize = 0;
    let mut v___x_2560_: usize = 0;
    let mut v___x_2561_: usize = 0;
    let mut v_h_2562_: usize = 0;
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: u64 = 0;
    let mut v_hash_2567_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2550_ = lean_array_get_size(v_keys_2546_);
                v___x_2551_ = lean_nat_dec_lt(v_i_2548_, v___x_2550_);
                if v___x_2551_ == 0 {
                    crate::leanh::lean_dec(v_i_2548_);
                    return v_entries_2549_;
                } else {
                    v_k_2552_ = lean_array_fget_borrowed(v_keys_2546_, v_i_2548_);
                    v_v_2553_ = lean_array_fget_borrowed(v_vals_2547_, v_i_2548_);
                    if crate::leanh::lean_obj_tag(v_k_2552_) == 0 {
                        v___x_2566_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_2555_ = v___x_2566_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2567_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_2552_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2555_ = v_hash_2567_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2556_ = lean_uint64_to_usize(v___y_2555_);
                v___x_2557_ = 5usize;
                v___x_2558_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2559_ = 1usize;
                v___x_2560_ = lean_usize_sub(v_depth_2545_, v___x_2559_);
                v___x_2561_ = lean_usize_mul(v___x_2557_, v___x_2560_);
                v_h_2562_ = lean_usize_shift_right(v_h_2556_, v___x_2561_);
                v___x_2563_ = lean_nat_add(v_i_2548_, v___x_2558_);
                crate::leanh::lean_dec(v_i_2548_);
                crate::leanh::lean_inc(v_v_2553_);
                crate::leanh::lean_inc(v_k_2552_);
                v___x_2564_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_entries_2549_, v_h_2562_, v_depth_2545_, v_k_2552_, v_v_2553_);
                v_i_2548_ = v___x_2563_;
                v_entries_2549_ = v___x_2564_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_2568_: *mut crate::leanh::LeanObject,
    mut v_keys_2569_: *mut crate::leanh::LeanObject,
    mut v_vals_2570_: *mut crate::leanh::LeanObject,
    mut v_i_2571_: *mut crate::leanh::LeanObject,
    mut v_entries_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2573_: usize = 0;
    let mut v_res_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2573_ = crate::leanh::lean_unbox_usize(v_depth_2568_);
    crate::leanh::lean_dec(v_depth_2568_);
    v_res_2574_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2573_, v_keys_2569_, v_vals_2570_, v_i_2571_, v_entries_2572_);
    crate::leanh::lean_dec_ref(v_vals_2570_);
    crate::leanh::lean_dec_ref(v_keys_2569_);
    return v_res_2574_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___boxed(
    mut v_x_2575_: *mut crate::leanh::LeanObject,
    mut v_x_2576_: *mut crate::leanh::LeanObject,
    mut v_x_2577_: *mut crate::leanh::LeanObject,
    mut v_x_2578_: *mut crate::leanh::LeanObject,
    mut v_x_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_379__boxed_2580_: usize = 0;
    let mut v_x_380__boxed_2581_: usize = 0;
    let mut v_res_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_379__boxed_2580_ = crate::leanh::lean_unbox_usize(v_x_2576_);
    crate::leanh::lean_dec(v_x_2576_);
    v_x_380__boxed_2581_ = crate::leanh::lean_unbox_usize(v_x_2577_);
    crate::leanh::lean_dec(v_x_2577_);
    v_res_2582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_2575_, v_x_379__boxed_2580_, v_x_380__boxed_2581_, v_x_2578_, v_x_2579_);
    return v_res_2582_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(
    mut v_x_2583_: *mut crate::leanh::LeanObject,
    mut v_x_2584_: *mut crate::leanh::LeanObject,
    mut v_x_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2587_: u64 = 0;
    let mut v___x_2588_: usize = 0;
    let mut v___x_2589_: usize = 0;
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: u64 = 0;
    let mut v_hash_2592_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2584_) == 0 {
                    v___x_2591_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_2587_ = v___x_2591_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2592_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_2584_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2587_ = v_hash_2592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2588_ = lean_uint64_to_usize(v___y_2587_);
                v___x_2589_ = 1usize;
                v___x_2590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_2583_, v___x_2588_, v___x_2589_, v_x_2584_, v_x_2585_);
                return v___x_2590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecState_addEntry(
    mut v_s_2593_: *mut crate::leanh::LeanObject,
    mut v_e_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_declName_2595_ = crate::leanh::lean_ctor_get(v_e_2594_, 0);
    crate::leanh::lean_inc(v_declName_2595_);
    v___x_2596_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_s_2593_, v_declName_2595_, v_e_2594_);
    return v___x_2596_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0(
    mut v_00_u03b2_2597_: *mut crate::leanh::LeanObject,
    mut v_x_2598_: *mut crate::leanh::LeanObject,
    mut v_x_2599_: *mut crate::leanh::LeanObject,
    mut v_x_2600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2601_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_x_2598_, v_x_2599_, v_x_2600_);
    return v___x_2601_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(
    mut v_00_u03b2_2602_: *mut crate::leanh::LeanObject,
    mut v_x_2603_: *mut crate::leanh::LeanObject,
    mut v_x_2604_: usize,
    mut v_x_2605_: usize,
    mut v_x_2606_: *mut crate::leanh::LeanObject,
    mut v_x_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2608_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_2603_, v_x_2604_, v_x_2605_, v_x_2606_, v_x_2607_);
    return v___x_2608_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___boxed(
    mut v_00_u03b2_2609_: *mut crate::leanh::LeanObject,
    mut v_x_2610_: *mut crate::leanh::LeanObject,
    mut v_x_2611_: *mut crate::leanh::LeanObject,
    mut v_x_2612_: *mut crate::leanh::LeanObject,
    mut v_x_2613_: *mut crate::leanh::LeanObject,
    mut v_x_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_576__boxed_2615_: usize = 0;
    let mut v_x_577__boxed_2616_: usize = 0;
    let mut v_res_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_576__boxed_2615_ = crate::leanh::lean_unbox_usize(v_x_2611_);
    crate::leanh::lean_dec(v_x_2611_);
    v_x_577__boxed_2616_ = crate::leanh::lean_unbox_usize(v_x_2612_);
    crate::leanh::lean_dec(v_x_2612_);
    v_res_2617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(v_00_u03b2_2609_, v_x_2610_, v_x_576__boxed_2615_, v_x_577__boxed_2616_, v_x_2613_, v_x_2614_);
    return v_res_2617_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2618_: *mut crate::leanh::LeanObject,
    mut v_n_2619_: *mut crate::leanh::LeanObject,
    mut v_k_2620_: *mut crate::leanh::LeanObject,
    mut v_v_2621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2622_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v_n_2619_, v_k_2620_, v_v_2621_);
    return v___x_2622_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2623_: *mut crate::leanh::LeanObject,
    mut v_depth_2624_: usize,
    mut v_keys_2625_: *mut crate::leanh::LeanObject,
    mut v_vals_2626_: *mut crate::leanh::LeanObject,
    mut v_heq_2627_: *mut crate::leanh::LeanObject,
    mut v_i_2628_: *mut crate::leanh::LeanObject,
    mut v_entries_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_2624_, v_keys_2625_, v_vals_2626_, v_i_2628_, v_entries_2629_);
    return v___x_2630_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2631_: *mut crate::leanh::LeanObject,
    mut v_depth_2632_: *mut crate::leanh::LeanObject,
    mut v_keys_2633_: *mut crate::leanh::LeanObject,
    mut v_vals_2634_: *mut crate::leanh::LeanObject,
    mut v_heq_2635_: *mut crate::leanh::LeanObject,
    mut v_i_2636_: *mut crate::leanh::LeanObject,
    mut v_entries_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2638_: usize = 0;
    let mut v_res_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2638_ = crate::leanh::lean_unbox_usize(v_depth_2632_);
    crate::leanh::lean_dec(v_depth_2632_);
    v_res_2639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(v_00_u03b2_2631_, v_depth_boxed_2638_, v_keys_2633_, v_vals_2634_, v_heq_2635_, v_i_2636_, v_entries_2637_);
    crate::leanh::lean_dec_ref(v_vals_2634_);
    crate::leanh::lean_dec_ref(v_keys_2633_);
    return v_res_2639_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2640_: *mut crate::leanh::LeanObject,
    mut v_x_2641_: *mut crate::leanh::LeanObject,
    mut v_x_2642_: *mut crate::leanh::LeanObject,
    mut v_x_2643_: *mut crate::leanh::LeanObject,
    mut v_x_2644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2641_, v_x_2642_, v_x_2643_, v_x_2644_);
    return v___x_2645_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(
    mut v_a_2646_: *mut crate::leanh::LeanObject,
    mut v_b_2647_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_declName_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    v_declName_2648_ = crate::leanh::lean_ctor_get(v_a_2646_, 0);
    v_declName_2649_ = crate::leanh::lean_ctor_get(v_b_2647_, 0);
    v___x_2650_ = l_Lean_Name_quickLt(v_declName_2648_, v_declName_2649_);
    return v___x_2650_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed(
    mut v_a_2651_: *mut crate::leanh::LeanObject,
    mut v_b_2652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2653_: u8 = 0;
    let mut v_r_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2653_ =
        l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(v_a_2651_, v_b_2652_);
    crate::leanh::lean_dec_ref(v_b_2652_);
    crate::leanh::lean_dec_ref(v_a_2651_);
    v_r_2654_ = crate::leanh::lean_box((v_res_2653_) as usize);
    return v_r_2654_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries(
    mut v_entries_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: u8 = 0;
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: u8 = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2657_ = lean_array_get_size(v_entries_2656_);
                v___x_2658_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2659_ = lean_nat_dec_eq(v___x_2657_, v___x_2658_);
                if v___x_2659_ == 0 {
                    v___x_2660_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0;
                    v___x_2661_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2662_ = lean_nat_sub(v___x_2657_, v___x_2661_);
                    v___x_2668_ = lean_nat_dec_le(v___x_2658_, v___x_2662_);
                    if v___x_2668_ == 0 {
                        crate::leanh::lean_inc(v___x_2662_);
                        v___y_2664_ = v___x_2662_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2664_ = v___x_2658_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_entries_2656_;
                }
            }
            1 => {
                v___x_2665_ = lean_nat_dec_le(v___y_2664_, v___x_2662_);
                if v___x_2665_ == 0 {
                    crate::leanh::lean_dec(v___x_2662_);
                    crate::leanh::lean_inc(v___y_2664_);
                    v___x_2666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        crate::leanh::lean_box(0),
                        v___x_2660_,
                        v___x_2657_,
                        v_entries_2656_,
                        v___y_2664_,
                        v___y_2664_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    crate::leanh::lean_dec(v___y_2664_);
                    return v___x_2666_;
                } else {
                    v___x_2667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        crate::leanh::lean_box(0),
                        v___x_2660_,
                        v___x_2657_,
                        v_entries_2656_,
                        v___y_2664_,
                        v___x_2662_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    crate::leanh::lean_dec(v___x_2662_);
                    return v___x_2667_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(
    mut v_entries_2672_: *mut crate::leanh::LeanObject,
    mut v_declName_2673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: u8 = 0;
    v___x_2674_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2675_ = lean_array_get_size(v_entries_2672_);
    v___x_2676_ = lean_nat_dec_lt(v___x_2674_, v___x_2675_);
    if v___x_2676_ == 0 {
        let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_declName_2673_);
        v___x_2677_ = crate::leanh::lean_box(0);
        return v___x_2677_;
    } else {
        let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2680_: u8 = 0;
        v___x_2678_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2679_ = lean_nat_sub(v___x_2675_, v___x_2678_);
        v___x_2680_ = lean_nat_dec_le(v___x_2674_, v___x_2679_);
        if v___x_2680_ == 0 {
            let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2679_);
            crate::leanh::lean_dec(v_declName_2673_);
            v___x_2681_ = crate::leanh::lean_box(0);
            return v___x_2681_;
        } else {
            let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2683_: u8 = 0;
            let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2682_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
            v___x_2683_ = 0;
            v___x_2684_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_2684_, 0, v_declName_2673_);
            crate::leanh::lean_ctor_set(v___x_2684_, 1, v___x_2682_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_2684_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                v___x_2683_,
            );
            v___x_2685_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0;
            v___x_2686_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1;
            v___x_2687_ = l_Array_binSearchAux___redArg(
                v___x_2685_,
                v___x_2686_,
                v_entries_2672_,
                v___x_2684_,
                v___x_2674_,
                v___x_2679_,
            );
            return v___x_2687_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___boxed(
    mut v_entries_2688_: *mut crate::leanh::LeanObject,
    mut v_declName_2689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(
        v_entries_2688_,
        v_declName_2689_,
    );
    crate::leanh::lean_dec_ref(v_entries_2688_);
    return v_res_2690_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_declName_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: u8 = 0;
    v_declName_2693_ = crate::leanh::lean_ctor_get(v___y_2691_, 0);
    v_declName_2694_ = crate::leanh::lean_ctor_get(v___y_2692_, 0);
    v___x_2695_ = l_Lean_Name_quickLt(v_declName_2693_, v_declName_2694_);
    return v___x_2695_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0___boxed(
    mut v___y_2696_: *mut crate::leanh::LeanObject,
    mut v___y_2697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2698_: u8 = 0;
    let mut v_r_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___y_2696_, v___y_2697_);
    crate::leanh::lean_dec_ref(v___y_2697_);
    crate::leanh::lean_dec_ref(v___y_2696_);
    v_r_2699_ = crate::leanh::lean_box((v_res_2698_) as usize);
    return v_r_2699_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_hi_2700_: *mut crate::leanh::LeanObject,
    mut v_pivot_2701_: *mut crate::leanh::LeanObject,
    mut v_as_2702_: *mut crate::leanh::LeanObject,
    mut v_i_2703_: *mut crate::leanh::LeanObject,
    mut v_k_2704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2705_: u8 = 0;
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: u8 = 0;
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2705_ = lean_nat_dec_lt(v_k_2704_, v_hi_2700_);
                if v___x_2705_ == 0 {
                    crate::leanh::lean_dec(v_k_2704_);
                    v___x_2706_ = lean_array_fswap(v_as_2702_, v_i_2703_, v_hi_2700_);
                    v___x_2707_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2707_, 0, v_i_2703_);
                    crate::leanh::lean_ctor_set(v___x_2707_, 1, v___x_2706_);
                    return v___x_2707_;
                } else {
                    v___x_2708_ = lean_array_fget_borrowed(v_as_2702_, v_k_2704_);
                    v_declName_2709_ = crate::leanh::lean_ctor_get(v___x_2708_, 0);
                    v_declName_2710_ = crate::leanh::lean_ctor_get(v_pivot_2701_, 0);
                    v___x_2711_ = l_Lean_Name_quickLt(v_declName_2709_, v_declName_2710_);
                    if v___x_2711_ == 0 {
                        v___x_2712_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2713_ = lean_nat_add(v_k_2704_, v___x_2712_);
                        crate::leanh::lean_dec(v_k_2704_);
                        v_k_2704_ = v___x_2713_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2715_ = lean_array_fswap(v_as_2702_, v_i_2703_, v_k_2704_);
                        v___x_2716_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2717_ = lean_nat_add(v_i_2703_, v___x_2716_);
                        crate::leanh::lean_dec(v_i_2703_);
                        v___x_2718_ = lean_nat_add(v_k_2704_, v___x_2716_);
                        crate::leanh::lean_dec(v_k_2704_);
                        v_as_2702_ = v___x_2715_;
                        v_i_2703_ = v___x_2717_;
                        v_k_2704_ = v___x_2718_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_hi_2720_: *mut crate::leanh::LeanObject,
    mut v_pivot_2721_: *mut crate::leanh::LeanObject,
    mut v_as_2722_: *mut crate::leanh::LeanObject,
    mut v_i_2723_: *mut crate::leanh::LeanObject,
    mut v_k_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_2720_, v_pivot_2721_, v_as_2722_, v_i_2723_, v_k_2724_);
    crate::leanh::lean_dec_ref(v_pivot_2721_);
    crate::leanh::lean_dec(v_hi_2720_);
    return v_res_2725_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(
    mut v_n_2726_: *mut crate::leanh::LeanObject,
    mut v_as_2727_: *mut crate::leanh::LeanObject,
    mut v_lo_2728_: *mut crate::leanh::LeanObject,
    mut v_hi_2729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: u8 = 0;
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: u8 = 0;
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: u8 = 0;
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: u8 = 0;
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2741_ = lean_nat_dec_lt(v_lo_2728_, v_hi_2729_);
                if v___x_2741_ == 0 {
                    crate::leanh::lean_dec(v_lo_2728_);
                    return v_as_2727_;
                } else {
                    v___x_2742_ = lean_nat_add(v_lo_2728_, v_hi_2729_);
                    v___x_2743_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_2744_ = lean_nat_shiftr(v___x_2742_, v___x_2743_);
                    crate::leanh::lean_dec(v___x_2742_);
                    v___x_2757_ = lean_array_fget_borrowed(v_as_2727_, v_mid_2744_);
                    v___x_2758_ = lean_array_fget_borrowed(v_as_2727_, v_lo_2728_);
                    v___x_2759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_2757_, v___x_2758_);
                    if v___x_2759_ == 0 {
                        v___y_2752_ = v_as_2727_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2760_ = lean_array_fswap(v_as_2727_, v_lo_2728_, v_mid_2744_);
                        v___y_2752_ = v___x_2760_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2732_ = lean_array_fget(v___y_2731_, v_hi_2729_);
                crate::leanh::lean_inc_n(v_lo_2728_, 2);
                v___x_2733_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_2729_, v_pivot_2732_, v___y_2731_, v_lo_2728_, v_lo_2728_);
                crate::leanh::lean_dec(v_pivot_2732_);
                v_fst_2734_ = crate::leanh::lean_ctor_get(v___x_2733_, 0);
                crate::leanh::lean_inc(v_fst_2734_);
                v_snd_2735_ = crate::leanh::lean_ctor_get(v___x_2733_, 1);
                crate::leanh::lean_inc(v_snd_2735_);
                crate::leanh::lean_dec_ref(v___x_2733_);
                v___x_2736_ = lean_nat_dec_le(v_hi_2729_, v_fst_2734_);
                if v___x_2736_ == 0 {
                    v___x_2737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_2726_, v_snd_2735_, v_lo_2728_, v_fst_2734_);
                    v___x_2738_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2739_ = lean_nat_add(v_fst_2734_, v___x_2738_);
                    crate::leanh::lean_dec(v_fst_2734_);
                    v_as_2727_ = v___x_2737_;
                    v_lo_2728_ = v___x_2739_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_2734_);
                    crate::leanh::lean_dec(v_lo_2728_);
                    return v_snd_2735_;
                }
            }
            2 => {
                v___x_2747_ = lean_array_fget_borrowed(v___y_2746_, v_mid_2744_);
                v___x_2748_ = lean_array_fget_borrowed(v___y_2746_, v_hi_2729_);
                v___x_2749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_2747_, v___x_2748_);
                if v___x_2749_ == 0 {
                    crate::leanh::lean_dec(v_mid_2744_);
                    v___y_2731_ = v___y_2746_;
                    state = 1;
                    continue;
                } else {
                    v___x_2750_ = lean_array_fswap(v___y_2746_, v_mid_2744_, v_hi_2729_);
                    crate::leanh::lean_dec(v_mid_2744_);
                    v___y_2731_ = v___x_2750_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2753_ = lean_array_fget_borrowed(v___y_2752_, v_hi_2729_);
                v___x_2754_ = lean_array_fget_borrowed(v___y_2752_, v_lo_2728_);
                v___x_2755_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_2753_, v___x_2754_);
                if v___x_2755_ == 0 {
                    v___y_2746_ = v___y_2752_;
                    state = 2;
                    continue;
                } else {
                    v___x_2756_ = lean_array_fswap(v___y_2752_, v_lo_2728_, v_hi_2729_);
                    v___y_2746_ = v___x_2756_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_n_2761_: *mut crate::leanh::LeanObject,
    mut v_as_2762_: *mut crate::leanh::LeanObject,
    mut v_lo_2763_: *mut crate::leanh::LeanObject,
    mut v_hi_2764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2765_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_2761_, v_as_2762_, v_lo_2763_, v_hi_2764_);
    crate::leanh::lean_dec(v_hi_2764_);
    crate::leanh::lean_dec(v_n_2761_);
    return v_res_2765_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(
    mut v_s_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: u8 = 0;
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: u8 = 0;
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2767_ = lean_array_mk(v_s_2766_);
                v___x_2768_ = lean_array_get_size(v___x_2767_);
                v___x_2769_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2770_ = lean_nat_dec_eq(v___x_2768_, v___x_2769_);
                if v___x_2770_ == 0 {
                    v___x_2771_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2772_ = lean_nat_sub(v___x_2768_, v___x_2771_);
                    v___x_2778_ = lean_nat_dec_le(v___x_2769_, v___x_2772_);
                    if v___x_2778_ == 0 {
                        crate::leanh::lean_inc(v___x_2772_);
                        v___y_2774_ = v___x_2772_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2774_ = v___x_2769_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2767_;
                }
            }
            1 => {
                v___x_2775_ = lean_nat_dec_le(v___y_2774_, v___x_2772_);
                if v___x_2775_ == 0 {
                    crate::leanh::lean_dec(v___x_2772_);
                    crate::leanh::lean_inc(v___y_2774_);
                    v___x_2776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_2768_, v___x_2767_, v___y_2774_, v___y_2774_);
                    crate::leanh::lean_dec(v___y_2774_);
                    return v___x_2776_;
                } else {
                    v___x_2777_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_2768_, v___x_2767_, v___y_2774_, v___x_2772_);
                    crate::leanh::lean_dec(v___x_2772_);
                    return v___x_2777_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(
    mut v_keys_2779_: *mut crate::leanh::LeanObject,
    mut v_i_2780_: *mut crate::leanh::LeanObject,
    mut v_k_2781_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: u8 = 0;
    let mut v_k_x27_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: u8 = 0;
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2782_ = lean_array_get_size(v_keys_2779_);
                v___x_2783_ = lean_nat_dec_lt(v_i_2780_, v___x_2782_);
                if v___x_2783_ == 0 {
                    crate::leanh::lean_dec(v_i_2780_);
                    return v___x_2783_;
                } else {
                    v_k_x27_2784_ = lean_array_fget_borrowed(v_keys_2779_, v_i_2780_);
                    v___x_2785_ = lean_name_eq(v_k_2781_, v_k_x27_2784_);
                    if v___x_2785_ == 0 {
                        v___x_2786_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2787_ = lean_nat_add(v_i_2780_, v___x_2786_);
                        crate::leanh::lean_dec(v_i_2780_);
                        v_i_2780_ = v___x_2787_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_2780_);
                        return v___x_2785_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_2789_: *mut crate::leanh::LeanObject,
    mut v_i_2790_: *mut crate::leanh::LeanObject,
    mut v_k_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2792_: u8 = 0;
    let mut v_r_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_2789_, v_i_2790_, v_k_2791_);
    crate::leanh::lean_dec(v_k_2791_);
    crate::leanh::lean_dec_ref(v_keys_2789_);
    v_r_2793_ = crate::leanh::lean_box((v_res_2792_) as usize);
    return v_r_2793_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_x_2794_: *mut crate::leanh::LeanObject,
    mut v_x_2795_: usize,
    mut v_x_2796_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: usize = 0;
    let mut v___x_2800_: usize = 0;
    let mut v___x_2801_: usize = 0;
    let mut v_j_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: u8 = 0;
    let mut v_node_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: usize = 0;
    let mut v___x_2809_: u8 = 0;
    let mut v_ks_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2794_) == 0 {
                    v_es_2797_ = crate::leanh::lean_ctor_get(v_x_2794_, 0);
                    v___x_2798_ = crate::leanh::lean_box(2);
                    v___x_2799_ = 5usize;
                    v___x_2800_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1);
                    v___x_2801_ = lean_usize_land(v_x_2795_, v___x_2800_);
                    v_j_2802_ = lean_usize_to_nat(v___x_2801_);
                    v___x_2803_ = lean_array_get_borrowed(v___x_2798_, v_es_2797_, v_j_2802_);
                    crate::leanh::lean_dec(v_j_2802_);
                    match crate::leanh::lean_obj_tag(v___x_2803_) {
                        0 => {
                            v_key_2804_ = crate::leanh::lean_ctor_get(v___x_2803_, 0);
                            v___x_2805_ = lean_name_eq(v_x_2796_, v_key_2804_);
                            return v___x_2805_;
                        }
                        1 => {
                            v_node_2806_ = crate::leanh::lean_ctor_get(v___x_2803_, 0);
                            v___x_2807_ = lean_usize_shift_right(v_x_2795_, v___x_2799_);
                            v_x_2794_ = v_node_2806_;
                            v_x_2795_ = v___x_2807_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2809_ = 0;
                            return v___x_2809_;
                        }
                    }
                } else {
                    v_ks_2810_ = crate::leanh::lean_ctor_get(v_x_2794_, 0);
                    v___x_2811_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2812_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_ks_2810_, v___x_2811_, v_x_2796_);
                    return v___x_2812_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(
    mut v_x_2813_: *mut crate::leanh::LeanObject,
    mut v_x_2814_: *mut crate::leanh::LeanObject,
    mut v_x_2815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_476__boxed_2816_: usize = 0;
    let mut v_res_2817_: u8 = 0;
    let mut v_r_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_476__boxed_2816_ = crate::leanh::lean_unbox_usize(v_x_2814_);
    crate::leanh::lean_dec(v_x_2814_);
    v_res_2817_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2813_, v_x_476__boxed_2816_, v_x_2815_);
    crate::leanh::lean_dec(v_x_2815_);
    crate::leanh::lean_dec_ref(v_x_2813_);
    v_r_2818_ = crate::leanh::lean_box((v_res_2817_) as usize);
    return v_r_2818_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_2819_: *mut crate::leanh::LeanObject,
    mut v_x_2820_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2822_: u64 = 0;
    let mut v___x_2823_: usize = 0;
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2825_: u64 = 0;
    let mut v_hash_2826_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2820_) == 0 {
                    v___x_2825_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_2822_ = v___x_2825_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2826_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_2820_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2822_ = v_hash_2826_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2823_ = lean_uint64_to_usize(v___y_2822_);
                v___x_2824_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2819_, v___x_2823_, v_x_2820_);
                return v___x_2824_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_x_2827_: *mut crate::leanh::LeanObject,
    mut v_x_2828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2829_: u8 = 0;
    let mut v_r_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2829_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_2827_, v_x_2828_);
    crate::leanh::lean_dec(v_x_2828_);
    crate::leanh::lean_dec_ref(v_x_2827_);
    v_r_2830_ = crate::leanh::lean_box((v_res_2829_) as usize);
    return v_r_2830_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(
    mut v_x1_2831_: *mut crate::leanh::LeanObject,
    mut v_x2_2832_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_declName_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: u8 = 0;
    v_declName_2833_ = crate::leanh::lean_ctor_get(v_x2_2832_, 0);
    v___x_2834_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x1_2831_, v_declName_2833_);
    if v___x_2834_ == 0 {
        let mut v___x_2835_: u8 = 0;
        v___x_2835_ = 1;
        return v___x_2835_;
    } else {
        let mut v___x_2836_: u8 = 0;
        v___x_2836_ = 0;
        return v___x_2836_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(
    mut v_x1_2837_: *mut crate::leanh::LeanObject,
    mut v_x2_2838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2839_: u8 = 0;
    let mut v_r_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2839_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x1_2837_, v_x2_2838_);
    crate::leanh::lean_dec_ref(v_x2_2838_);
    crate::leanh::lean_dec_ref(v_x1_2837_);
    v_r_2840_ = crate::leanh::lean_box((v_res_2839_) as usize);
    return v_r_2840_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(
    mut v_x_2841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2842_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1,
    );
    return v___x_2842_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(
    mut v_x_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2844_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x_2843_);
    crate::leanh::lean_dec_ref(v_x_2843_);
    return v_res_2844_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_;
    v___x_2873_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2872_);
    return v___x_2873_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(
    mut v_a_2874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2875_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
    return v_res_2875_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(
    mut v_n_2876_: *mut crate::leanh::LeanObject,
    mut v_as_2877_: *mut crate::leanh::LeanObject,
    mut v_lo_2878_: *mut crate::leanh::LeanObject,
    mut v_hi_2879_: *mut crate::leanh::LeanObject,
    mut v_w_2880_: *mut crate::leanh::LeanObject,
    mut v_hlo_2881_: *mut crate::leanh::LeanObject,
    mut v_hhi_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2883_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_2876_, v_as_2877_, v_lo_2878_, v_hi_2879_);
    return v___x_2883_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___boxed(
    mut v_n_2884_: *mut crate::leanh::LeanObject,
    mut v_as_2885_: *mut crate::leanh::LeanObject,
    mut v_lo_2886_: *mut crate::leanh::LeanObject,
    mut v_hi_2887_: *mut crate::leanh::LeanObject,
    mut v_w_2888_: *mut crate::leanh::LeanObject,
    mut v_hlo_2889_: *mut crate::leanh::LeanObject,
    mut v_hhi_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(v_n_2884_, v_as_2885_, v_lo_2886_, v_hi_2887_, v_w_2888_, v_hlo_2889_, v_hhi_2890_);
    crate::leanh::lean_dec(v_hi_2887_);
    crate::leanh::lean_dec(v_n_2884_);
    return v_res_2891_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(
    mut v_00_u03b2_2892_: *mut crate::leanh::LeanObject,
    mut v_x_2893_: *mut crate::leanh::LeanObject,
    mut v_x_2894_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2895_: u8 = 0;
    v___x_2895_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_2893_, v_x_2894_);
    return v___x_2895_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b2_2896_: *mut crate::leanh::LeanObject,
    mut v_x_2897_: *mut crate::leanh::LeanObject,
    mut v_x_2898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2899_: u8 = 0;
    let mut v_r_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2899_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(v_00_u03b2_2896_, v_x_2897_, v_x_2898_);
    crate::leanh::lean_dec(v_x_2898_);
    crate::leanh::lean_dec_ref(v_x_2897_);
    v_r_2900_ = crate::leanh::lean_box((v_res_2899_) as usize);
    return v_r_2900_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(
    mut v_n_2901_: *mut crate::leanh::LeanObject,
    mut v_lo_2902_: *mut crate::leanh::LeanObject,
    mut v_hi_2903_: *mut crate::leanh::LeanObject,
    mut v_hhi_2904_: *mut crate::leanh::LeanObject,
    mut v_pivot_2905_: *mut crate::leanh::LeanObject,
    mut v_as_2906_: *mut crate::leanh::LeanObject,
    mut v_i_2907_: *mut crate::leanh::LeanObject,
    mut v_k_2908_: *mut crate::leanh::LeanObject,
    mut v_ilo_2909_: *mut crate::leanh::LeanObject,
    mut v_ik_2910_: *mut crate::leanh::LeanObject,
    mut v_w_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2912_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_2903_, v_pivot_2905_, v_as_2906_, v_i_2907_, v_k_2908_);
    return v___x_2912_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_n_2913_: *mut crate::leanh::LeanObject,
    mut v_lo_2914_: *mut crate::leanh::LeanObject,
    mut v_hi_2915_: *mut crate::leanh::LeanObject,
    mut v_hhi_2916_: *mut crate::leanh::LeanObject,
    mut v_pivot_2917_: *mut crate::leanh::LeanObject,
    mut v_as_2918_: *mut crate::leanh::LeanObject,
    mut v_i_2919_: *mut crate::leanh::LeanObject,
    mut v_k_2920_: *mut crate::leanh::LeanObject,
    mut v_ilo_2921_: *mut crate::leanh::LeanObject,
    mut v_ik_2922_: *mut crate::leanh::LeanObject,
    mut v_w_2923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2924_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(v_n_2913_, v_lo_2914_, v_hi_2915_, v_hhi_2916_, v_pivot_2917_, v_as_2918_, v_i_2919_, v_k_2920_, v_ilo_2921_, v_ik_2922_, v_w_2923_);
    crate::leanh::lean_dec_ref(v_pivot_2917_);
    crate::leanh::lean_dec(v_hi_2915_);
    crate::leanh::lean_dec(v_lo_2914_);
    crate::leanh::lean_dec(v_n_2913_);
    return v_res_2924_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(
    mut v_00_u03b2_2925_: *mut crate::leanh::LeanObject,
    mut v_x_2926_: *mut crate::leanh::LeanObject,
    mut v_x_2927_: usize,
    mut v_x_2928_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2929_: u8 = 0;
    v___x_2929_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2926_, v_x_2927_, v_x_2928_);
    return v___x_2929_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_00_u03b2_2930_: *mut crate::leanh::LeanObject,
    mut v_x_2931_: *mut crate::leanh::LeanObject,
    mut v_x_2932_: *mut crate::leanh::LeanObject,
    mut v_x_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_656__boxed_2934_: usize = 0;
    let mut v_res_2935_: u8 = 0;
    let mut v_r_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_656__boxed_2934_ = crate::leanh::lean_unbox_usize(v_x_2932_);
    crate::leanh::lean_dec(v_x_2932_);
    v_res_2935_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_2930_, v_x_2931_, v_x_656__boxed_2934_, v_x_2933_);
    crate::leanh::lean_dec(v_x_2933_);
    crate::leanh::lean_dec_ref(v_x_2931_);
    v_r_2936_ = crate::leanh::lean_box((v_res_2935_) as usize);
    return v_r_2936_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(
    mut v_00_u03b2_2937_: *mut crate::leanh::LeanObject,
    mut v_keys_2938_: *mut crate::leanh::LeanObject,
    mut v_vals_2939_: *mut crate::leanh::LeanObject,
    mut v_heq_2940_: *mut crate::leanh::LeanObject,
    mut v_i_2941_: *mut crate::leanh::LeanObject,
    mut v_k_2942_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2943_: u8 = 0;
    v___x_2943_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_2938_, v_i_2941_, v_k_2942_);
    return v___x_2943_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_2944_: *mut crate::leanh::LeanObject,
    mut v_keys_2945_: *mut crate::leanh::LeanObject,
    mut v_vals_2946_: *mut crate::leanh::LeanObject,
    mut v_heq_2947_: *mut crate::leanh::LeanObject,
    mut v_i_2948_: *mut crate::leanh::LeanObject,
    mut v_k_2949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2950_: u8 = 0;
    let mut v_r_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03b2_2944_, v_keys_2945_, v_vals_2946_, v_heq_2947_, v_i_2948_, v_k_2949_);
    crate::leanh::lean_dec(v_k_2949_);
    crate::leanh::lean_dec_ref(v_vals_2946_);
    crate::leanh::lean_dec_ref(v_keys_2945_);
    v_r_2951_ = crate::leanh::lean_box((v_res_2950_) as usize);
    return v_r_2951_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(
    mut v_env_2952_: *mut crate::leanh::LeanObject,
    mut v_type_2953_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_body_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_type_2953_) == 7 {
                    v_body_2954_ = crate::leanh::lean_ctor_get(v_type_2953_, 2);
                    v_type_2953_ = v_body_2954_;
                    state = 0;
                    continue;
                } else {
                    v___x_2956_ = l_Lean_Expr_getAppFn(v_type_2953_);
                    if crate::leanh::lean_obj_tag(v___x_2956_) == 4 {
                        v_declName_2957_ = crate::leanh::lean_ctor_get(v___x_2956_, 0);
                        crate::leanh::lean_inc(v_declName_2957_);
                        crate::leanh::lean_dec_ref_known(v___x_2956_, 2);
                        v___x_2958_ =
                            l_Lean_Compiler_hasNospecializeAttribute(v_env_2952_, v_declName_2957_);
                        return v___x_2958_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2956_);
                        crate::leanh::lean_dec_ref(v_env_2952_);
                        v___x_2959_ = 0;
                        return v___x_2959_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType___boxed(
    mut v_env_2960_: *mut crate::leanh::LeanObject,
    mut v_type_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2962_: u8 = 0;
    let mut v_r_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2962_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(
        v_env_2960_,
        v_type_2961_,
    );
    crate::leanh::lean_dec_ref(v_type_2961_);
    v_r_2963_ = crate::leanh::lean_box((v_res_2962_) as usize);
    return v_r_2963_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(
    mut v_env_2964_: *mut crate::leanh::LeanObject,
    mut v_type_2965_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_body_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: u8 = 0;
    let mut v___x_2971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_type_2965_) == 7 {
                    v_body_2966_ = crate::leanh::lean_ctor_get(v_type_2965_, 2);
                    v_type_2965_ = v_body_2966_;
                    state = 0;
                    continue;
                } else {
                    v___x_2968_ = l_Lean_Expr_getAppFn(v_type_2965_);
                    if crate::leanh::lean_obj_tag(v___x_2968_) == 4 {
                        v_declName_2969_ = crate::leanh::lean_ctor_get(v___x_2968_, 0);
                        crate::leanh::lean_inc(v_declName_2969_);
                        crate::leanh::lean_dec_ref_known(v___x_2968_, 2);
                        v___x_2970_ = l_Lean_Compiler_hasWeakSpecializeAttribute(
                            v_env_2964_,
                            v_declName_2969_,
                        );
                        return v___x_2970_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2968_);
                        crate::leanh::lean_dec_ref(v_env_2964_);
                        v___x_2971_ = 0;
                        return v___x_2971_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType___boxed(
    mut v_env_2972_: *mut crate::leanh::LeanObject,
    mut v_type_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2974_: u8 = 0;
    let mut v_r_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2974_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(
        v_env_2972_,
        v_type_2973_,
    );
    crate::leanh::lean_dec_ref(v_type_2973_);
    v_r_2975_ = crate::leanh::lean_box((v_res_2974_) as usize);
    return v_r_2975_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(
    mut v___x_2979_: *mut crate::leanh::LeanObject,
    mut v_param_2980_: *mut crate::leanh::LeanObject,
    mut v_paramsInfo_2981_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2982_: *mut crate::leanh::LeanObject,
    mut v_a_2983_: *mut crate::leanh::LeanObject,
    mut v_b_2984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weak_3005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2990_ = lean_nat_dec_lt(v_a_2983_, v_upperBound_2982_);
                if v___x_2990_ == 0 {
                    crate::leanh::lean_dec(v_a_2983_);
                    crate::leanh::lean_inc_ref(v_b_2984_);
                    return v_b_2984_;
                } else {
                    v___x_2991_ = crate::leanh::lean_box(0);
                    v___x_2992_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0;
                    v___x_3001_ = l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default;
                    v___x_3004_ =
                        lean_array_get_borrowed(v___x_3001_, v_paramsInfo_2981_, v_a_2983_);
                    match crate::leanh::lean_obj_tag(v___x_3004_) {
                        0 => {
                            v_weak_3005_ = crate::leanh::lean_ctor_get_uint8(v___x_3004_, 0 as u32);
                            if v_weak_3005_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                state = 3;
                                continue;
                            }
                        }
                        2 => {
                            state = 3;
                            continue;
                        }
                        4 => {
                            state = 3;
                            continue;
                        }
                        _ => {
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2987_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2988_ = lean_nat_add(v_a_2983_, v___x_2987_);
                crate::leanh::lean_dec(v_a_2983_);
                v_a_2983_ = v___x_2988_;
                v_b_2984_ = v_a_2986_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2994_ = lean_array_fget_borrowed(v___x_2979_, v_a_2983_);
                v_type_2995_ = crate::leanh::lean_ctor_get(v___x_2994_, 2);
                v_fvarId_2996_ = crate::leanh::lean_ctor_get(v_param_2980_, 0);
                v___x_2997_ = l_Lean_Expr_containsFVar(v_type_2995_, v_fvarId_2996_);
                if v___x_2997_ == 0 {
                    v_a_2986_ = v___x_2992_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_2983_);
                    v___x_2998_ = crate::leanh::lean_box((v___x_2997_) as usize);
                    v___x_2999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2999_, 0, v___x_2998_);
                    v___x_3000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3000_, 0, v___x_2999_);
                    crate::leanh::lean_ctor_set(v___x_3000_, 1, v___x_2991_);
                    return v___x_3000_;
                }
            }
            3 => {
                v___x_3003_ = lean_array_get_borrowed(v___x_3001_, v_paramsInfo_2981_, v_a_2983_);
                if crate::leanh::lean_obj_tag(v___x_3003_) == 0 {
                    state = 2;
                    continue;
                } else {
                    v_a_2986_ = v___x_2992_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___boxed(
    mut v___x_3006_: *mut crate::leanh::LeanObject,
    mut v_param_3007_: *mut crate::leanh::LeanObject,
    mut v_paramsInfo_3008_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3009_: *mut crate::leanh::LeanObject,
    mut v_a_3010_: *mut crate::leanh::LeanObject,
    mut v_b_3011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3012_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_3006_, v_param_3007_, v_paramsInfo_3008_, v_upperBound_3009_, v_a_3010_, v_b_3011_);
    crate::leanh::lean_dec_ref(v_b_3011_);
    crate::leanh::lean_dec(v_upperBound_3009_);
    crate::leanh::lean_dec_ref(v_paramsInfo_3008_);
    crate::leanh::lean_dec_ref(v_param_3007_);
    crate::leanh::lean_dec_ref(v___x_3006_);
    return v_res_3012_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3013_ = 0;
    v___x_3014_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_3013_);
    return v___x_3014_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(
    mut v_decl_3015_: *mut crate::leanh::LeanObject,
    mut v_paramsInfo_3016_: *mut crate::leanh::LeanObject,
    mut v_j_3017_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toSignature_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_param_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSignature_3018_ = crate::leanh::lean_ctor_get(v_decl_3015_, 0);
    v_params_3019_ = crate::leanh::lean_ctor_get(v_toSignature_3018_, 3);
    v___x_3020_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0);
    v___x_3021_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3022_ = lean_nat_add(v_j_3017_, v___x_3021_);
    v___x_3023_ = lean_array_get_size(v_params_3019_);
    v___x_3024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0;
    v_param_3025_ = lean_array_get_borrowed(v___x_3020_, v_params_3019_, v_j_3017_);
    v___x_3026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v_params_3019_, v_param_3025_, v_paramsInfo_3016_, v___x_3023_, v___x_3022_, v___x_3024_);
    v_fst_3027_ = crate::leanh::lean_ctor_get(v___x_3026_, 0);
    crate::leanh::lean_inc(v_fst_3027_);
    crate::leanh::lean_dec_ref(v___x_3026_);
    if crate::leanh::lean_obj_tag(v_fst_3027_) == 0 {
        let mut v___x_3028_: u8 = 0;
        v___x_3028_ = 0;
        return v___x_3028_;
    } else {
        let mut v_val_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3030_: u8 = 0;
        v_val_3029_ = crate::leanh::lean_ctor_get(v_fst_3027_, 0);
        crate::leanh::lean_inc(v_val_3029_);
        crate::leanh::lean_dec_ref_known(v_fst_3027_, 1);
        v___x_3030_ = (crate::leanh::lean_unbox(v_val_3029_) as u8);
        crate::leanh::lean_dec(v_val_3029_);
        return v___x_3030_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___boxed(
    mut v_decl_3031_: *mut crate::leanh::LeanObject,
    mut v_paramsInfo_3032_: *mut crate::leanh::LeanObject,
    mut v_j_3033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3034_: u8 = 0;
    let mut v_r_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3034_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(
        v_decl_3031_,
        v_paramsInfo_3032_,
        v_j_3033_,
    );
    crate::leanh::lean_dec(v_j_3033_);
    crate::leanh::lean_dec_ref(v_paramsInfo_3032_);
    crate::leanh::lean_dec_ref(v_decl_3031_);
    v_r_3035_ = crate::leanh::lean_box((v_res_3034_) as usize);
    return v_r_3035_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(
    mut v___x_3036_: *mut crate::leanh::LeanObject,
    mut v_param_3037_: *mut crate::leanh::LeanObject,
    mut v_paramsInfo_3038_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3039_: *mut crate::leanh::LeanObject,
    mut v_inst_3040_: *mut crate::leanh::LeanObject,
    mut v_R_3041_: *mut crate::leanh::LeanObject,
    mut v_a_3042_: *mut crate::leanh::LeanObject,
    mut v_b_3043_: *mut crate::leanh::LeanObject,
    mut v_c_3044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_3036_, v_param_3037_, v_paramsInfo_3038_, v_upperBound_3039_, v_a_3042_, v_b_3043_);
    return v___x_3045_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___boxed(
    mut v___x_3046_: *mut crate::leanh::LeanObject,
    mut v_param_3047_: *mut crate::leanh::LeanObject,
    mut v_paramsInfo_3048_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3049_: *mut crate::leanh::LeanObject,
    mut v_inst_3050_: *mut crate::leanh::LeanObject,
    mut v_R_3051_: *mut crate::leanh::LeanObject,
    mut v_a_3052_: *mut crate::leanh::LeanObject,
    mut v_b_3053_: *mut crate::leanh::LeanObject,
    mut v_c_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(v___x_3046_, v_param_3047_, v_paramsInfo_3048_, v_upperBound_3049_, v_inst_3050_, v_R_3051_, v_a_3052_, v_b_3053_, v_c_3054_);
    crate::leanh::lean_dec_ref(v_b_3053_);
    crate::leanh::lean_dec(v_upperBound_3049_);
    crate::leanh::lean_dec_ref(v_paramsInfo_3048_);
    crate::leanh::lean_dec_ref(v_param_3047_);
    crate::leanh::lean_dec_ref(v___x_3046_);
    return v_res_3055_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3056_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3056_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(
    mut v_msg_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3070_: u8 = 0;
    let mut v_toFunctor_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3077_: u8 = 0;
    let mut v___f_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11117__overap_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3098_: u8 = 0;
    let mut v_unused_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3100_: u8 = 0;
    let mut v_unused_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3065_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0);
                v___x_3066_ = l_StateRefT_x27_instMonad___redArg(v___x_3065_);
                v_toApplicative_3067_ = crate::leanh::lean_ctor_get(v___x_3066_, 0);
                v_isSharedCheck_3100_ = (!crate::leanh::lean_is_exclusive(v___x_3066_)) as u8;
                if v_isSharedCheck_3100_ == 0 {
                    v_unused_3101_ = crate::leanh::lean_ctor_get(v___x_3066_, 1);
                    crate::leanh::lean_dec(v_unused_3101_);
                    v___x_3069_ = v___x_3066_;
                    v_isShared_3070_ = v_isSharedCheck_3100_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3067_);
                    crate::leanh::lean_dec(v___x_3066_);
                    v___x_3069_ = crate::leanh::lean_box(0);
                    v_isShared_3070_ = v_isSharedCheck_3100_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3071_ = crate::leanh::lean_ctor_get(v_toApplicative_3067_, 0);
                v_toSeq_3072_ = crate::leanh::lean_ctor_get(v_toApplicative_3067_, 2);
                v_toSeqLeft_3073_ = crate::leanh::lean_ctor_get(v_toApplicative_3067_, 3);
                v_toSeqRight_3074_ = crate::leanh::lean_ctor_get(v_toApplicative_3067_, 4);
                v_isSharedCheck_3098_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3067_)) as u8;
                if v_isSharedCheck_3098_ == 0 {
                    v_unused_3099_ = crate::leanh::lean_ctor_get(v_toApplicative_3067_, 1);
                    crate::leanh::lean_dec(v_unused_3099_);
                    v___x_3076_ = v_toApplicative_3067_;
                    v_isShared_3077_ = v_isSharedCheck_3098_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3074_);
                    crate::leanh::lean_inc(v_toSeqLeft_3073_);
                    crate::leanh::lean_inc(v_toSeq_3072_);
                    crate::leanh::lean_inc(v_toFunctor_3071_);
                    crate::leanh::lean_dec(v_toApplicative_3067_);
                    v___x_3076_ = crate::leanh::lean_box(0);
                    v_isShared_3077_ = v_isSharedCheck_3098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3078_ =
                    l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1;
                v___f_3079_ =
                    l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_3071_);
                v___f_3080_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3080_, 0, v_toFunctor_3071_);
                v___f_3081_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3081_, 0, v_toFunctor_3071_);
                v___x_3082_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3082_, 0, v___f_3080_);
                crate::leanh::lean_ctor_set(v___x_3082_, 1, v___f_3081_);
                v___f_3083_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3083_, 0, v_toSeqRight_3074_);
                v___f_3084_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3084_, 0, v_toSeqLeft_3073_);
                v___f_3085_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3085_, 0, v_toSeq_3072_);
                if v_isShared_3077_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3076_, 4, v___f_3083_);
                    crate::leanh::lean_ctor_set(v___x_3076_, 3, v___f_3084_);
                    crate::leanh::lean_ctor_set(v___x_3076_, 2, v___f_3085_);
                    crate::leanh::lean_ctor_set(v___x_3076_, 1, v___f_3078_);
                    crate::leanh::lean_ctor_set(v___x_3076_, 0, v___x_3082_);
                    v___x_3087_ = v___x_3076_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3097_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___f_3078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 2, v___f_3085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 3, v___f_3084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 4, v___f_3083_);
                    v___x_3087_ = v_reuseFailAlloc_3097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 1, v___f_3079_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3087_);
                    v___x_3089_ = v___x_3069_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 1, v___f_3079_);
                    v___x_3089_ = v_reuseFailAlloc_3096_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3090_ = l_StateRefT_x27_instMonad___redArg(v___x_3089_);
                v___x_3091_ = crate::leanh::lean_box(0);
                v___x_3092_ = l_instInhabitedOfMonad___redArg(v___x_3090_, v___x_3091_);
                v___f_3093_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3093_, 0, v___x_3092_);
                v___x_11117__overap_3094_ = lean_panic_fn_borrowed(v___f_3093_, v_msg_3059_);
                crate::leanh::lean_dec_ref(v___f_3093_);
                crate::leanh::lean_inc(v___y_3063_);
                crate::leanh::lean_inc_ref(v___y_3062_);
                crate::leanh::lean_inc(v___y_3061_);
                crate::leanh::lean_inc_ref(v___y_3060_);
                v___x_3095_ = crate::leanh::lean_apply_5(
                    v___x_11117__overap_3094_,
                    v___y_3060_,
                    v___y_3061_,
                    v___y_3062_,
                    v___y_3063_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___boxed(
    mut v_msg_3102_: *mut crate::leanh::LeanObject,
    mut v___y_3103_: *mut crate::leanh::LeanObject,
    mut v___y_3104_: *mut crate::leanh::LeanObject,
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3108_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(
        v_msg_3102_,
        v___y_3103_,
        v___y_3104_,
        v___y_3105_,
        v___y_3106_,
    );
    crate::leanh::lean_dec(v___y_3106_);
    crate::leanh::lean_dec_ref(v___y_3105_);
    crate::leanh::lean_dec(v___y_3104_);
    crate::leanh::lean_dec_ref(v___y_3103_);
    return v_res_3108_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(
    mut v_a_3109_: *mut crate::leanh::LeanObject,
    mut v_as_3110_: *mut crate::leanh::LeanObject,
    mut v_i_3111_: usize,
    mut v_stop_3112_: usize,
) -> u8 {
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: usize = 0;
    let mut v___x_3117_: usize = 0;
    let mut v___x_3119_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3113_ = lean_usize_dec_eq(v_i_3111_, v_stop_3112_);
                if v___x_3113_ == 0 {
                    v___x_3114_ = lean_array_uget_borrowed(v_as_3110_, v_i_3111_);
                    v___x_3115_ = lean_nat_dec_eq(v_a_3109_, v___x_3114_);
                    if v___x_3115_ == 0 {
                        v___x_3116_ = 1usize;
                        v___x_3117_ = lean_usize_add(v_i_3111_, v___x_3116_);
                        v_i_3111_ = v___x_3117_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3115_;
                    }
                } else {
                    v___x_3119_ = 0;
                    return v___x_3119_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0___boxed(
    mut v_a_3120_: *mut crate::leanh::LeanObject,
    mut v_as_3121_: *mut crate::leanh::LeanObject,
    mut v_i_3122_: *mut crate::leanh::LeanObject,
    mut v_stop_3123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3124_: usize = 0;
    let mut v_stop_boxed_3125_: usize = 0;
    let mut v_res_3126_: u8 = 0;
    let mut v_r_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3124_ = crate::leanh::lean_unbox_usize(v_i_3122_);
    crate::leanh::lean_dec(v_i_3122_);
    v_stop_boxed_3125_ = crate::leanh::lean_unbox_usize(v_stop_3123_);
    crate::leanh::lean_dec(v_stop_3123_);
    v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(v_a_3120_, v_as_3121_, v_i_boxed_3124_, v_stop_boxed_3125_);
    crate::leanh::lean_dec_ref(v_as_3121_);
    crate::leanh::lean_dec(v_a_3120_);
    v_r_3127_ = crate::leanh::lean_box((v_res_3126_) as usize);
    return v_r_3127_;
}
pub unsafe fn l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(
    mut v_as_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: u8 = 0;
    v___x_3130_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3131_ = lean_array_get_size(v_as_3128_);
    v___x_3132_ = lean_nat_dec_lt(v___x_3130_, v___x_3131_);
    if v___x_3132_ == 0 {
        return v___x_3132_;
    } else {
        if v___x_3132_ == 0 {
            return v___x_3132_;
        } else {
            let mut v___x_3133_: usize = 0;
            let mut v___x_3134_: usize = 0;
            let mut v___x_3135_: u8 = 0;
            v___x_3133_ = 0usize;
            v___x_3134_ = lean_usize_of_nat(v___x_3131_);
            v___x_3135_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(v_a_3129_, v_as_3128_, v___x_3133_, v___x_3134_);
            return v___x_3135_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0___boxed(
    mut v_as_3136_: *mut crate::leanh::LeanObject,
    mut v_a_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3138_: u8 = 0;
    let mut v_r_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3138_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(
        v_as_3136_, v_a_3137_,
    );
    crate::leanh::lean_dec(v_a_3137_);
    crate::leanh::lean_dec_ref(v_as_3136_);
    v_r_3139_ = crate::leanh::lean_box((v_res_3138_) as usize);
    return v_r_3139_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(
    mut v_b_3140_: *mut crate::leanh::LeanObject,
    mut v_info_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
    mut v___y_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3147_ = lean_array_push(v_b_3140_, v_info_3141_);
    v___x_3148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3148_, 0, v___x_3147_);
    v___x_3149_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3149_, 0, v___x_3148_);
    return v___x_3149_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0___boxed(
    mut v_b_3150_: *mut crate::leanh::LeanObject,
    mut v_info_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
    mut v___y_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3157_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3150_, v_info_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
    crate::leanh::lean_dec(v___y_3155_);
    crate::leanh::lean_dec_ref(v___y_3154_);
    crate::leanh::lean_dec(v___y_3153_);
    crate::leanh::lean_dec_ref(v___y_3152_);
    return v_res_3157_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(
    mut v_upperBound_3160_: *mut crate::leanh::LeanObject,
    mut v___x_3161_: *mut crate::leanh::LeanObject,
    mut v_autoSpecialize_3162_: *mut crate::leanh::LeanObject,
    mut v___x_3163_: *mut crate::leanh::LeanObject,
    mut v___x_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
    mut v_b_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
    mut v___y_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v_a_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_a_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v___x_3195_: u8 = 0;
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: u8 = 0;
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v_val_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v_a_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3195_ = lean_nat_dec_lt(v_a_3165_, v_upperBound_3160_);
                if v___x_3195_ == 0 {
                    crate::leanh::lean_dec(v_a_3165_);
                    crate::leanh::lean_dec(v___x_3164_);
                    crate::leanh::lean_dec(v___x_3163_);
                    crate::leanh::lean_dec_ref(v_autoSpecialize_3162_);
                    v___x_3196_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3196_, 0, v_b_3166_);
                    return v___x_3196_;
                } else {
                    v___x_3197_ = lean_st_ref_get(v___y_3170_);
                    v___x_3198_ = lean_array_fget_borrowed(v___x_3161_, v_a_3165_);
                    v_type_3199_ = crate::leanh::lean_ctor_get(v___x_3198_, 2);
                    crate::leanh::lean_inc_ref(v_type_3199_);
                    v___x_3200_ =
                        l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_3199_, v___y_3170_);
                    if crate::leanh::lean_obj_tag(v___x_3200_) == 0 {
                        v_a_3201_ = crate::leanh::lean_ctor_get(v___x_3200_, 0);
                        crate::leanh::lean_inc(v_a_3201_);
                        crate::leanh::lean_dec_ref_known(v___x_3200_, 1);
                        v_env_3202_ = crate::leanh::lean_ctor_get(v___x_3197_, 0);
                        crate::leanh::lean_inc_ref(v_env_3202_);
                        crate::leanh::lean_dec(v___x_3197_);
                        if crate::leanh::lean_obj_tag(v___x_3164_) == 0 {
                            v___x_3226_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0;
                            v___x_3227_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v___x_3226_, v_a_3165_);
                            v___y_3213_ = v___x_3227_;
                            state = 8;
                            continue;
                        } else {
                            v_val_3228_ = crate::leanh::lean_ctor_get(v___x_3164_, 0);
                            v___x_3229_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_val_3228_, v_a_3165_);
                            v___y_3213_ = v___x_3229_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3197_);
                        crate::leanh::lean_dec_ref(v_b_3166_);
                        crate::leanh::lean_dec(v_a_3165_);
                        crate::leanh::lean_dec(v___x_3164_);
                        crate::leanh::lean_dec(v___x_3163_);
                        crate::leanh::lean_dec_ref(v_autoSpecialize_3162_);
                        v_a_3230_ = crate::leanh::lean_ctor_get(v___x_3200_, 0);
                        v_isSharedCheck_3237_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3200_)) as u8;
                        if v_isSharedCheck_3237_ == 0 {
                            v___x_3232_ = v___x_3200_;
                            v_isShared_3233_ = v_isSharedCheck_3237_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3230_);
                            crate::leanh::lean_dec(v___x_3200_);
                            v___x_3232_ = crate::leanh::lean_box(0);
                            v_isShared_3233_ = v_isSharedCheck_3237_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3173_) == 0 {
                    v_a_3174_ = crate::leanh::lean_ctor_get(v___y_3173_, 0);
                    v_isSharedCheck_3186_ = (!crate::leanh::lean_is_exclusive(v___y_3173_)) as u8;
                    if v_isSharedCheck_3186_ == 0 {
                        v___x_3176_ = v___y_3173_;
                        v_isShared_3177_ = v_isSharedCheck_3186_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3174_);
                        crate::leanh::lean_dec(v___y_3173_);
                        v___x_3176_ = crate::leanh::lean_box(0);
                        v_isShared_3177_ = v_isSharedCheck_3186_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3165_);
                    crate::leanh::lean_dec(v___x_3164_);
                    crate::leanh::lean_dec(v___x_3163_);
                    crate::leanh::lean_dec_ref(v_autoSpecialize_3162_);
                    v_a_3187_ = crate::leanh::lean_ctor_get(v___y_3173_, 0);
                    v_isSharedCheck_3194_ = (!crate::leanh::lean_is_exclusive(v___y_3173_)) as u8;
                    if v_isSharedCheck_3194_ == 0 {
                        v___x_3189_ = v___y_3173_;
                        v_isShared_3190_ = v_isSharedCheck_3194_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3187_);
                        crate::leanh::lean_dec(v___y_3173_);
                        v___x_3189_ = crate::leanh::lean_box(0);
                        v_isShared_3190_ = v_isSharedCheck_3194_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3174_) == 0 {
                    crate::leanh::lean_dec(v_a_3165_);
                    crate::leanh::lean_dec(v___x_3164_);
                    crate::leanh::lean_dec(v___x_3163_);
                    crate::leanh::lean_dec_ref(v_autoSpecialize_3162_);
                    v_a_3178_ = crate::leanh::lean_ctor_get(v_a_3174_, 0);
                    crate::leanh::lean_inc(v_a_3178_);
                    crate::leanh::lean_dec_ref_known(v_a_3174_, 1);
                    if v_isShared_3177_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3176_, 0, v_a_3178_);
                        v___x_3180_ = v___x_3176_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3178_);
                        v___x_3180_ = v_reuseFailAlloc_3181_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3176_);
                    v_a_3182_ = crate::leanh::lean_ctor_get(v_a_3174_, 0);
                    crate::leanh::lean_inc(v_a_3182_);
                    crate::leanh::lean_dec_ref_known(v_a_3174_, 1);
                    v___x_3183_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3184_ = lean_nat_add(v_a_3165_, v___x_3183_);
                    crate::leanh::lean_dec(v_a_3165_);
                    v_a_3165_ = v___x_3184_;
                    v_b_3166_ = v_a_3182_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_3180_;
            }
            4 => {
                if v_isShared_3190_ == 0 {
                    v___x_3192_ = v___x_3189_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
                    v___x_3192_ = v_reuseFailAlloc_3193_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3192_;
            }
            6 => {
                v___x_3204_ = crate::leanh::lean_box(4);
                v___x_3205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3166_, v___x_3204_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                v___y_3173_ = v___x_3205_;
                state = 1;
                continue;
            }
            7 => {
                v___x_3207_ = lean_st_ref_get(v___y_3170_);
                v_env_3208_ = crate::leanh::lean_ctor_get(v___x_3207_, 0);
                crate::leanh::lean_inc_ref(v_env_3208_);
                crate::leanh::lean_dec(v___x_3207_);
                v___x_3209_ =
                    l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(
                        v_env_3208_,
                        v_type_3199_,
                    );
                v___x_3210_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_3210_, 0 as u32, v___x_3209_);
                v___x_3211_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3166_, v___x_3210_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                v___y_3173_ = v___x_3211_;
                state = 1;
                continue;
            }
            8 => {
                if v___y_3213_ == 0 {
                    v___x_3214_ =
                        l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(
                            v_env_3202_,
                            v_type_3199_,
                        );
                    if v___x_3214_ == 0 {
                        crate::leanh::lean_inc_ref(v_type_3199_);
                        v___x_3215_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_3199_);
                        if v___x_3215_ == 0 {
                            if crate::leanh::lean_obj_tag(v_a_3201_) == 0 {
                                if v___x_3215_ == 0 {
                                    crate::leanh::lean_inc_ref(v_autoSpecialize_3162_);
                                    crate::leanh::lean_inc(v___x_3164_);
                                    crate::leanh::lean_inc(v___x_3163_);
                                    v___x_3216_ = crate::leanh::lean_apply_2(
                                        v_autoSpecialize_3162_,
                                        v___x_3163_,
                                        v___x_3164_,
                                    );
                                    v___x_3217_ = (crate::leanh::lean_unbox(v___x_3216_) as u8);
                                    if v___x_3217_ == 0 {
                                        state = 6;
                                        continue;
                                    } else {
                                        if crate::leanh::lean_obj_tag(v_type_3199_) == 7 {
                                            v___x_3218_ = crate::leanh::lean_box(1);
                                            v___x_3219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3166_, v___x_3218_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                                            v___y_3173_ = v___x_3219_;
                                            state = 1;
                                            continue;
                                        } else {
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_a_3201_, 1);
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3201_);
                            v___x_3220_ = crate::leanh::lean_box(2);
                            v___x_3221_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3166_, v___x_3220_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                            v___y_3173_ = v___x_3221_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3201_);
                        v___x_3222_ = crate::leanh::lean_box(4);
                        v___x_3223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3166_, v___x_3222_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                        v___y_3173_ = v___x_3223_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3202_);
                    crate::leanh::lean_dec(v_a_3201_);
                    v___x_3224_ = crate::leanh::lean_box(3);
                    v___x_3225_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3166_, v___x_3224_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                    v___y_3173_ = v___x_3225_;
                    state = 1;
                    continue;
                }
            }
            9 => {
                if v_isShared_3233_ == 0 {
                    v___x_3235_ = v___x_3232_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
                    v___x_3235_ = v_reuseFailAlloc_3236_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___boxed(
    mut v_upperBound_3238_: *mut crate::leanh::LeanObject,
    mut v___x_3239_: *mut crate::leanh::LeanObject,
    mut v_autoSpecialize_3240_: *mut crate::leanh::LeanObject,
    mut v___x_3241_: *mut crate::leanh::LeanObject,
    mut v___x_3242_: *mut crate::leanh::LeanObject,
    mut v_a_3243_: *mut crate::leanh::LeanObject,
    mut v_b_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3250_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v_upperBound_3238_, v___x_3239_, v_autoSpecialize_3240_, v___x_3241_, v___x_3242_, v_a_3243_, v_b_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
    crate::leanh::lean_dec(v___y_3248_);
    crate::leanh::lean_dec_ref(v___y_3247_);
    crate::leanh::lean_dec(v___y_3246_);
    crate::leanh::lean_dec_ref(v___y_3245_);
    crate::leanh::lean_dec_ref(v___x_3239_);
    crate::leanh::lean_dec(v_upperBound_3238_);
    return v_res_3250_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(
    mut v_autoSpecialize_3251_: *mut crate::leanh::LeanObject,
    mut v_as_3252_: *mut crate::leanh::LeanObject,
    mut v_sz_3253_: usize,
    mut v_i_3254_: usize,
    mut v_b_3255_: *mut crate::leanh::LeanObject,
    mut v___y_3256_: *mut crate::leanh::LeanObject,
    mut v___y_3257_: *mut crate::leanh::LeanObject,
    mut v___y_3258_: *mut crate::leanh::LeanObject,
    mut v___y_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: usize = 0;
    let mut v___x_3264_: usize = 0;
    let mut v___x_3266_: u8 = 0;
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: u8 = 0;
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3266_ = lean_usize_dec_lt(v_i_3254_, v_sz_3253_);
                if v___x_3266_ == 0 {
                    crate::leanh::lean_dec_ref(v_autoSpecialize_3251_);
                    v___x_3267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3267_, 0, v_b_3255_);
                    return v___x_3267_;
                } else {
                    v___x_3268_ = lean_st_ref_get(v___y_3259_);
                    v_env_3269_ = crate::leanh::lean_ctor_get(v___x_3268_, 0);
                    crate::leanh::lean_inc_ref(v_env_3269_);
                    crate::leanh::lean_dec(v___x_3268_);
                    v_a_3270_ = lean_array_uget_borrowed(v_as_3252_, v_i_3254_);
                    v_toSignature_3271_ = crate::leanh::lean_ctor_get(v_a_3270_, 0);
                    v_name_3272_ = crate::leanh::lean_ctor_get(v_toSignature_3271_, 0);
                    v_params_3273_ = crate::leanh::lean_ctor_get(v_toSignature_3271_, 3);
                    crate::leanh::lean_inc(v_name_3272_);
                    v___x_3274_ =
                        l_Lean_Compiler_hasNospecializeAttribute(v_env_3269_, v_name_3272_);
                    if v___x_3274_ == 0 {
                        v___x_3275_ = lean_st_ref_get(v___y_3259_);
                        v_env_3276_ = crate::leanh::lean_ctor_get(v___x_3275_, 0);
                        crate::leanh::lean_inc_ref(v_env_3276_);
                        crate::leanh::lean_dec(v___x_3275_);
                        v___x_3277_ = lean_array_get_size(v_params_3273_);
                        v___x_3278_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3279_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
                        crate::leanh::lean_inc_n(v_name_3272_, 2);
                        v___x_3280_ =
                            l_Lean_Compiler_getSpecializationArgs_x3f(v_env_3276_, v_name_3272_);
                        crate::leanh::lean_inc_ref(v_autoSpecialize_3251_);
                        v___x_3281_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v___x_3277_, v_params_3273_, v_autoSpecialize_3251_, v_name_3272_, v___x_3280_, v___x_3278_, v___x_3279_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
                        if crate::leanh::lean_obj_tag(v___x_3281_) == 0 {
                            v_a_3282_ = crate::leanh::lean_ctor_get(v___x_3281_, 0);
                            crate::leanh::lean_inc(v_a_3282_);
                            crate::leanh::lean_dec_ref_known(v___x_3281_, 1);
                            v___x_3283_ = lean_array_push(v_b_3255_, v_a_3282_);
                            v_a_3262_ = v___x_3283_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_3255_);
                            crate::leanh::lean_dec_ref(v_autoSpecialize_3251_);
                            v_a_3284_ = crate::leanh::lean_ctor_get(v___x_3281_, 0);
                            v_isSharedCheck_3291_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3281_)) as u8;
                            if v_isSharedCheck_3291_ == 0 {
                                v___x_3286_ = v___x_3281_;
                                v_isShared_3287_ = v_isSharedCheck_3291_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3284_);
                                crate::leanh::lean_dec(v___x_3281_);
                                v___x_3286_ = crate::leanh::lean_box(0);
                                v_isShared_3287_ = v_isSharedCheck_3291_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___x_3292_ = lean_array_get_size(v_params_3273_);
                        v___x_3293_ = crate::leanh::lean_box(4);
                        v___x_3294_ = lean_mk_array(v___x_3292_, v___x_3293_);
                        v___x_3295_ = lean_array_push(v_b_3255_, v___x_3294_);
                        v_a_3262_ = v___x_3295_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3263_ = 1usize;
                v___x_3264_ = lean_usize_add(v_i_3254_, v___x_3263_);
                v_i_3254_ = v___x_3264_;
                v_b_3255_ = v_a_3262_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3287_ == 0 {
                    v___x_3289_ = v___x_3286_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
                    v___x_3289_ = v_reuseFailAlloc_3290_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3___boxed(
    mut v_autoSpecialize_3296_: *mut crate::leanh::LeanObject,
    mut v_as_3297_: *mut crate::leanh::LeanObject,
    mut v_sz_3298_: *mut crate::leanh::LeanObject,
    mut v_i_3299_: *mut crate::leanh::LeanObject,
    mut v_b_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
    mut v___y_3302_: *mut crate::leanh::LeanObject,
    mut v___y_3303_: *mut crate::leanh::LeanObject,
    mut v___y_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3306_: usize = 0;
    let mut v_i_boxed_3307_: usize = 0;
    let mut v_res_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3306_ = crate::leanh::lean_unbox_usize(v_sz_3298_);
    crate::leanh::lean_dec(v_sz_3298_);
    v_i_boxed_3307_ = crate::leanh::lean_unbox_usize(v_i_3299_);
    crate::leanh::lean_dec(v_i_3299_);
    v_res_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_3296_, v_as_3297_, v_sz_boxed_3306_, v_i_boxed_3307_, v_b_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
    crate::leanh::lean_dec(v___y_3304_);
    crate::leanh::lean_dec_ref(v___y_3303_);
    crate::leanh::lean_dec(v___y_3302_);
    crate::leanh::lean_dec_ref(v___y_3301_);
    crate::leanh::lean_dec_ref(v_as_3297_);
    return v_res_3308_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(
    mut v_as_3309_: *mut crate::leanh::LeanObject,
    mut v_i_3310_: usize,
    mut v_stop_3311_: usize,
) -> u8 {
    let mut v___x_3312_: u8 = 0;
    let mut v___x_3313_: u8 = 0;
    let mut v___y_3315_: u8 = 0;
    let mut v___x_3316_: usize = 0;
    let mut v___x_3317_: usize = 0;
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weak_3320_: u8 = 0;
    let mut v___x_3321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3312_ = lean_usize_dec_eq(v_i_3310_, v_stop_3311_);
                if v___x_3312_ == 0 {
                    v___x_3313_ = 1;
                    v___x_3319_ = lean_array_uget_borrowed(v_as_3309_, v_i_3310_);
                    match crate::leanh::lean_obj_tag(v___x_3319_) {
                        0 => {
                            v_weak_3320_ = crate::leanh::lean_ctor_get_uint8(v___x_3319_, 0 as u32);
                            if v_weak_3320_ == 0 {
                                return v___x_3313_;
                            } else {
                                v___y_3315_ = v___x_3312_;
                                state = 1;
                                continue;
                            }
                        }
                        2 => {
                            v___y_3315_ = v___x_3312_;
                            state = 1;
                            continue;
                        }
                        4 => {
                            v___y_3315_ = v___x_3312_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            return v___x_3313_;
                        }
                    }
                } else {
                    v___x_3321_ = 0;
                    return v___x_3321_;
                }
            }
            1 => {
                if v___y_3315_ == 0 {
                    v___x_3316_ = 1usize;
                    v___x_3317_ = lean_usize_add(v_i_3310_, v___x_3316_);
                    v_i_3310_ = v___x_3317_;
                    state = 0;
                    continue;
                } else {
                    return v___x_3313_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2___boxed(
    mut v_as_3322_: *mut crate::leanh::LeanObject,
    mut v_i_3323_: *mut crate::leanh::LeanObject,
    mut v_stop_3324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3325_: usize = 0;
    let mut v_stop_boxed_3326_: usize = 0;
    let mut v_res_3327_: u8 = 0;
    let mut v_r_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3325_ = crate::leanh::lean_unbox_usize(v_i_3323_);
    crate::leanh::lean_dec(v_i_3323_);
    v_stop_boxed_3326_ = crate::leanh::lean_unbox_usize(v_stop_3324_);
    crate::leanh::lean_dec(v_stop_3324_);
    v_res_3327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_as_3322_, v_i_boxed_3325_, v_stop_boxed_3326_);
    crate::leanh::lean_dec_ref(v_as_3322_);
    v_r_3328_ = crate::leanh::lean_box((v_res_3327_) as usize);
    return v_r_3328_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(
    mut v_as_3329_: *mut crate::leanh::LeanObject,
    mut v_i_3330_: usize,
    mut v_stop_3331_: usize,
) -> u8 {
    let mut v___x_3332_: u8 = 0;
    let mut v___x_3333_: u8 = 0;
    let mut v___y_3335_: u8 = 0;
    let mut v___x_3336_: usize = 0;
    let mut v___x_3337_: usize = 0;
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: u8 = 0;
    let mut v___x_3343_: usize = 0;
    let mut v___x_3344_: usize = 0;
    let mut v___x_3345_: u8 = 0;
    let mut v___x_3346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3332_ = lean_usize_dec_eq(v_i_3330_, v_stop_3331_);
                if v___x_3332_ == 0 {
                    v___x_3333_ = 1;
                    v___x_3339_ = lean_array_uget_borrowed(v_as_3329_, v_i_3330_);
                    v___x_3340_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3341_ = lean_array_get_size(v___x_3339_);
                    v___x_3342_ = lean_nat_dec_lt(v___x_3340_, v___x_3341_);
                    if v___x_3342_ == 0 {
                        v___y_3335_ = v___x_3332_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_3342_ == 0 {
                            v___y_3335_ = v___x_3332_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3343_ = 0usize;
                            v___x_3344_ = lean_usize_of_nat(v___x_3341_);
                            v___x_3345_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v___x_3339_, v___x_3343_, v___x_3344_);
                            v___y_3335_ = v___x_3345_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3346_ = 0;
                    return v___x_3346_;
                }
            }
            1 => {
                if v___y_3335_ == 0 {
                    v___x_3336_ = 1usize;
                    v___x_3337_ = lean_usize_add(v_i_3330_, v___x_3336_);
                    v_i_3330_ = v___x_3337_;
                    state = 0;
                    continue;
                } else {
                    return v___x_3333_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5___boxed(
    mut v_as_3347_: *mut crate::leanh::LeanObject,
    mut v_i_3348_: *mut crate::leanh::LeanObject,
    mut v_stop_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3350_: usize = 0;
    let mut v_stop_boxed_3351_: usize = 0;
    let mut v_res_3352_: u8 = 0;
    let mut v_r_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3350_ = crate::leanh::lean_unbox_usize(v_i_3348_);
    crate::leanh::lean_dec(v_i_3348_);
    v_stop_boxed_3351_ = crate::leanh::lean_unbox_usize(v_stop_3349_);
    crate::leanh::lean_dec(v_stop_3349_);
    v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_as_3347_, v_i_boxed_3350_, v_stop_boxed_3351_);
    crate::leanh::lean_dec_ref(v_as_3347_);
    v_r_3353_ = crate::leanh::lean_box((v_res_3352_) as usize);
    return v_r_3353_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(
    mut v_as_3354_: *mut crate::leanh::LeanObject,
    mut v_bs_3355_: *mut crate::leanh::LeanObject,
    mut v_i_3356_: *mut crate::leanh::LeanObject,
    mut v_cs_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: u8 = 0;
    let mut v_a_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: u8 = 0;
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3364_ = lean_array_get_size(v_as_3354_);
                v___x_3365_ = lean_nat_dec_lt(v_i_3356_, v___x_3364_);
                if v___x_3365_ == 0 {
                    crate::leanh::lean_dec(v_i_3356_);
                    return v_cs_3357_;
                } else {
                    v___x_3366_ = lean_array_get_size(v_bs_3355_);
                    v___x_3367_ = lean_nat_dec_lt(v_i_3356_, v___x_3366_);
                    if v___x_3367_ == 0 {
                        crate::leanh::lean_dec(v_i_3356_);
                        return v_cs_3357_;
                    } else {
                        v_a_3368_ = lean_array_fget_borrowed(v_as_3354_, v_i_3356_);
                        v_b_3369_ = lean_array_fget_borrowed(v_bs_3355_, v_i_3356_);
                        v___x_3370_ = (crate::leanh::lean_unbox(v_b_3369_) as u8);
                        if v___x_3370_ == 0 {
                            if crate::leanh::lean_obj_tag(v_a_3368_) == 3 {
                                v___y_3359_ = v_a_3368_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3371_ = crate::leanh::lean_box(4);
                                v___y_3359_ = v___x_3371_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc(v_a_3368_);
                            v___y_3359_ = v_a_3368_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3360_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3361_ = lean_nat_add(v_i_3356_, v___x_3360_);
                crate::leanh::lean_dec(v_i_3356_);
                v___x_3362_ = lean_array_push(v_cs_3357_, v___y_3359_);
                v_i_3356_ = v___x_3361_;
                v_cs_3357_ = v___x_3362_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6___boxed(
    mut v_as_3372_: *mut crate::leanh::LeanObject,
    mut v_bs_3373_: *mut crate::leanh::LeanObject,
    mut v_i_3374_: *mut crate::leanh::LeanObject,
    mut v_cs_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3376_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(
        v_as_3372_, v_bs_3373_, v_i_3374_, v_cs_3375_,
    );
    crate::leanh::lean_dec_ref(v_bs_3373_);
    crate::leanh::lean_dec_ref(v_as_3372_);
    return v_res_3376_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(
    mut v_upperBound_3377_: *mut crate::leanh::LeanObject,
    mut v___x_3378_: *mut crate::leanh::LeanObject,
    mut v_a_3379_: *mut crate::leanh::LeanObject,
    mut v_b_3380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3387_ = lean_nat_dec_lt(v_a_3379_, v_upperBound_3377_);
                if v___x_3387_ == 0 {
                    crate::leanh::lean_dec(v_a_3379_);
                    v___x_3388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3388_, 0, v_b_3380_);
                    return v___x_3388_;
                } else {
                    v___x_3389_ = l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default;
                    v___x_3390_ = lean_array_get_borrowed(v___x_3389_, v_b_3380_, v_a_3379_);
                    if crate::leanh::lean_obj_tag(v___x_3390_) == 2 {
                        v___x_3391_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v___x_3378_, v_b_3380_, v_a_3379_);
                        if v___x_3391_ == 0 {
                            v___x_3392_ = crate::leanh::lean_box(4);
                            v___x_3393_ = lean_array_set(v_b_3380_, v_a_3379_, v___x_3392_);
                            v_a_3383_ = v___x_3393_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3383_ = v_b_3380_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3383_ = v_b_3380_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3384_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3385_ = lean_nat_add(v_a_3379_, v___x_3384_);
                crate::leanh::lean_dec(v_a_3379_);
                v_a_3379_ = v___x_3385_;
                v_b_3380_ = v_a_3383_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg___boxed(
    mut v_upperBound_3394_: *mut crate::leanh::LeanObject,
    mut v___x_3395_: *mut crate::leanh::LeanObject,
    mut v_a_3396_: *mut crate::leanh::LeanObject,
    mut v_b_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3399_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_3394_, v___x_3395_, v_a_3396_, v_b_3397_);
    crate::leanh::lean_dec_ref(v___x_3395_);
    crate::leanh::lean_dec(v_upperBound_3394_);
    return v_res_3399_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_3400_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3;
    v___x_3405_ = crate::leanh::lean_unsigned_to_nat(43);
    v___x_3406_ = crate::leanh::lean_unsigned_to_nat(236);
    v___x_3407_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2;
    v___x_3408_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1;
    v___x_3409_ = l_mkPanicMessageWithDecl(
        v___x_3408_,
        v___x_3407_,
        v___x_3406_,
        v___x_3405_,
        v___x_3404_,
    );
    return v___x_3409_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(
    mut v_upperBound_3410_: *mut crate::leanh::LeanObject,
    mut v_decls_3411_: *mut crate::leanh::LeanObject,
    mut v_alreadySpecialized_3412_: *mut crate::leanh::LeanObject,
    mut v___x_3413_: *mut crate::leanh::LeanObject,
    mut v_a_3414_: *mut crate::leanh::LeanObject,
    mut v_a_3415_: *mut crate::leanh::LeanObject,
    mut v_b_3416_: *mut crate::leanh::LeanObject,
    mut v___y_3417_: *mut crate::leanh::LeanObject,
    mut v___y_3418_: *mut crate::leanh::LeanObject,
    mut v___y_3419_: *mut crate::leanh::LeanObject,
    mut v___y_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3461_: u8 = 0;
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3427_ = lean_nat_dec_lt(v_a_3415_, v_upperBound_3410_);
                if v___x_3427_ == 0 {
                    crate::leanh::lean_dec(v_a_3415_);
                    v___x_3428_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3428_, 0, v_b_3416_);
                    return v___x_3428_;
                } else {
                    v___x_3429_ = lean_array_fget_borrowed(v_decls_3411_, v_a_3415_);
                    v_toSignature_3430_ = crate::leanh::lean_ctor_get(v___x_3429_, 0);
                    v_name_3431_ = crate::leanh::lean_ctor_get(v_toSignature_3430_, 0);
                    v___x_3432_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3413_, v_name_3431_);
                    if crate::leanh::lean_obj_tag(v___x_3432_) == 1 {
                        v_val_3433_ = crate::leanh::lean_ctor_get(v___x_3432_, 0);
                        crate::leanh::lean_inc(v_val_3433_);
                        crate::leanh::lean_dec_ref_known(v___x_3432_, 1);
                        v___x_3434_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0);
                        v___x_3435_ = lean_array_get_borrowed(v___x_3434_, v_a_3414_, v_a_3415_);
                        v___x_3436_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3437_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
                        v___x_3438_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v___x_3435_, v_val_3433_, v___x_3436_, v___x_3437_);
                        crate::leanh::lean_dec(v_val_3433_);
                        v___x_3439_ = lean_array_get_size(v___x_3438_);
                        v___x_3440_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v___x_3439_, v___x_3429_, v___x_3436_, v___x_3438_);
                        if crate::leanh::lean_obj_tag(v___x_3440_) == 0 {
                            v_a_3441_ = crate::leanh::lean_ctor_get(v___x_3440_, 0);
                            crate::leanh::lean_inc(v_a_3441_);
                            crate::leanh::lean_dec_ref_known(v___x_3440_, 1);
                            v___x_3442_ = 0;
                            v___x_3443_ = crate::leanh::lean_box((v___x_3442_) as usize);
                            v___x_3444_ =
                                lean_array_get(v___x_3443_, v_alreadySpecialized_3412_, v_a_3415_);
                            crate::leanh::lean_dec(v___x_3443_);
                            crate::leanh::lean_inc(v_name_3431_);
                            v___x_3445_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_3445_, 0, v_name_3431_);
                            crate::leanh::lean_ctor_set(v___x_3445_, 1, v_a_3441_);
                            v___x_3446_ = (crate::leanh::lean_unbox(v___x_3444_) as u8);
                            crate::leanh::lean_dec(v___x_3444_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_3445_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v___x_3446_,
                            );
                            v___x_3447_ = lean_array_push(v_b_3416_, v___x_3445_);
                            v_a_3423_ = v___x_3447_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_3416_);
                            crate::leanh::lean_dec(v_a_3415_);
                            v_a_3448_ = crate::leanh::lean_ctor_get(v___x_3440_, 0);
                            v_isSharedCheck_3455_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3440_)) as u8;
                            if v_isSharedCheck_3455_ == 0 {
                                v___x_3450_ = v___x_3440_;
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3448_);
                                crate::leanh::lean_dec(v___x_3440_);
                                v___x_3450_ = crate::leanh::lean_box(0);
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3432_);
                        v___x_3456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4);
                        v___x_3457_ =
                            l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(
                                v___x_3456_,
                                v___y_3417_,
                                v___y_3418_,
                                v___y_3419_,
                                v___y_3420_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3457_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3457_, 1);
                            v_a_3423_ = v_b_3416_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_3416_);
                            crate::leanh::lean_dec(v_a_3415_);
                            v_a_3458_ = crate::leanh::lean_ctor_get(v___x_3457_, 0);
                            v_isSharedCheck_3465_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3457_)) as u8;
                            if v_isSharedCheck_3465_ == 0 {
                                v___x_3460_ = v___x_3457_;
                                v_isShared_3461_ = v_isSharedCheck_3465_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3458_);
                                crate::leanh::lean_dec(v___x_3457_);
                                v___x_3460_ = crate::leanh::lean_box(0);
                                v_isShared_3461_ = v_isSharedCheck_3465_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3424_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3425_ = lean_nat_add(v_a_3415_, v___x_3424_);
                crate::leanh::lean_dec(v_a_3415_);
                v_a_3415_ = v___x_3425_;
                v_b_3416_ = v_a_3423_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3451_ == 0 {
                    v___x_3453_ = v___x_3450_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3453_;
            }
            4 => {
                if v_isShared_3461_ == 0 {
                    v___x_3463_ = v___x_3460_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3464_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
                    v___x_3463_ = v_reuseFailAlloc_3464_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___boxed(
    mut v_upperBound_3466_: *mut crate::leanh::LeanObject,
    mut v_decls_3467_: *mut crate::leanh::LeanObject,
    mut v_alreadySpecialized_3468_: *mut crate::leanh::LeanObject,
    mut v___x_3469_: *mut crate::leanh::LeanObject,
    mut v_a_3470_: *mut crate::leanh::LeanObject,
    mut v_a_3471_: *mut crate::leanh::LeanObject,
    mut v_b_3472_: *mut crate::leanh::LeanObject,
    mut v___y_3473_: *mut crate::leanh::LeanObject,
    mut v___y_3474_: *mut crate::leanh::LeanObject,
    mut v___y_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3478_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_3466_, v_decls_3467_, v_alreadySpecialized_3468_, v___x_3469_, v_a_3470_, v_a_3471_, v_b_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
    crate::leanh::lean_dec(v___y_3476_);
    crate::leanh::lean_dec_ref(v___y_3475_);
    crate::leanh::lean_dec(v___y_3474_);
    crate::leanh::lean_dec_ref(v___y_3473_);
    crate::leanh::lean_dec_ref(v_a_3470_);
    crate::leanh::lean_dec(v___x_3469_);
    crate::leanh::lean_dec_ref(v_alreadySpecialized_3468_);
    crate::leanh::lean_dec_ref(v_decls_3467_);
    crate::leanh::lean_dec(v_upperBound_3466_);
    return v_res_3478_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(
    mut v_alreadySpecialized_3479_: *mut crate::leanh::LeanObject,
    mut v_as_3480_: *mut crate::leanh::LeanObject,
    mut v_i_3481_: *mut crate::leanh::LeanObject,
    mut v_j_3482_: *mut crate::leanh::LeanObject,
    mut v_bs_3483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3485_: u8 = 0;
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3484_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3485_ = lean_nat_dec_eq(v_i_3481_, v_zero_3484_);
                if v_isZero_3485_ == 1 {
                    crate::leanh::lean_dec(v_j_3482_);
                    crate::leanh::lean_dec(v_i_3481_);
                    return v_bs_3483_;
                } else {
                    v___x_3486_ = lean_array_fget_borrowed(v_as_3480_, v_j_3482_);
                    v_toSignature_3487_ = crate::leanh::lean_ctor_get(v___x_3486_, 0);
                    v_name_3488_ = crate::leanh::lean_ctor_get(v_toSignature_3487_, 0);
                    v_params_3489_ = crate::leanh::lean_ctor_get(v_toSignature_3487_, 3);
                    v_one_3490_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3491_ = lean_nat_sub(v_i_3481_, v_one_3490_);
                    crate::leanh::lean_dec(v_i_3481_);
                    v___x_3492_ = lean_array_get_size(v_params_3489_);
                    v___x_3493_ = crate::leanh::lean_box(4);
                    v___x_3494_ = lean_mk_array(v___x_3492_, v___x_3493_);
                    v___x_3495_ = crate::leanh::lean_box((v_isZero_3485_) as usize);
                    v___x_3496_ =
                        lean_array_get(v___x_3495_, v_alreadySpecialized_3479_, v_j_3482_);
                    crate::leanh::lean_dec(v___x_3495_);
                    crate::leanh::lean_inc(v_name_3488_);
                    v___x_3497_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3497_, 0, v_name_3488_);
                    crate::leanh::lean_ctor_set(v___x_3497_, 1, v___x_3494_);
                    v___x_3498_ = (crate::leanh::lean_unbox(v___x_3496_) as u8);
                    crate::leanh::lean_dec(v___x_3496_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3497_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_3498_,
                    );
                    v___x_3499_ = lean_nat_add(v_j_3482_, v_one_3490_);
                    crate::leanh::lean_dec(v_j_3482_);
                    v___x_3500_ = lean_array_push(v_bs_3483_, v___x_3497_);
                    v_i_3481_ = v_n_3491_;
                    v_j_3482_ = v___x_3499_;
                    v_bs_3483_ = v___x_3500_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg___boxed(
    mut v_alreadySpecialized_3502_: *mut crate::leanh::LeanObject,
    mut v_as_3503_: *mut crate::leanh::LeanObject,
    mut v_i_3504_: *mut crate::leanh::LeanObject,
    mut v_j_3505_: *mut crate::leanh::LeanObject,
    mut v_bs_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3507_ =
        l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(
            v_alreadySpecialized_3502_,
            v_as_3503_,
            v_i_3504_,
            v_j_3505_,
            v_bs_3506_,
        );
    crate::leanh::lean_dec_ref(v_as_3503_);
    crate::leanh::lean_dec_ref(v_alreadySpecialized_3502_);
    return v_res_3507_;
}
pub unsafe fn l_Lean_Compiler_LCNF_computeSpecEntries(
    mut v_decls_3510_: *mut crate::leanh::LeanObject,
    mut v_autoSpecialize_3511_: *mut crate::leanh::LeanObject,
    mut v_alreadySpecialized_3512_: *mut crate::leanh::LeanObject,
    mut v_a_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declsInfo_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3520_: usize = 0;
    let mut v___x_3521_: usize = 0;
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: u8 = 0;
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v_a_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3546_: u8 = 0;
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3518_ = crate::leanh::lean_unsigned_to_nat(0);
                v_declsInfo_3519_ = l_Lean_Compiler_LCNF_computeSpecEntries___closed__0;
                v_sz_3520_ = lean_array_size(v_decls_3510_);
                v___x_3521_ = 0usize;
                v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_3511_, v_decls_3510_, v_sz_3520_, v___x_3521_, v_declsInfo_3519_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
                if crate::leanh::lean_obj_tag(v___x_3522_) == 0 {
                    v_a_3523_ = crate::leanh::lean_ctor_get(v___x_3522_, 0);
                    v_isSharedCheck_3542_ = (!crate::leanh::lean_is_exclusive(v___x_3522_)) as u8;
                    if v_isSharedCheck_3542_ == 0 {
                        v___x_3525_ = v___x_3522_;
                        v_isShared_3526_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3523_);
                        crate::leanh::lean_dec(v___x_3522_);
                        v___x_3525_ = crate::leanh::lean_box(0);
                        v_isShared_3526_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decls_3510_);
                    v_a_3543_ = crate::leanh::lean_ctor_get(v___x_3522_, 0);
                    v_isSharedCheck_3550_ = (!crate::leanh::lean_is_exclusive(v___x_3522_)) as u8;
                    if v_isSharedCheck_3550_ == 0 {
                        v___x_3545_ = v___x_3522_;
                        v_isShared_3546_ = v_isSharedCheck_3550_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3543_);
                        crate::leanh::lean_dec(v___x_3522_);
                        v___x_3545_ = crate::leanh::lean_box(0);
                        v_isShared_3546_ = v_isSharedCheck_3550_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3534_ = lean_array_get_size(v_a_3523_);
                v___x_3535_ = lean_nat_dec_lt(v___x_3518_, v___x_3534_);
                if v___x_3535_ == 0 {
                    crate::leanh::lean_dec(v_a_3523_);
                    state = 2;
                    continue;
                } else {
                    if v___x_3535_ == 0 {
                        crate::leanh::lean_dec(v_a_3523_);
                        state = 2;
                        continue;
                    } else {
                        v___x_3536_ = lean_usize_of_nat(v___x_3534_);
                        v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_a_3523_, v___x_3521_, v___x_3536_);
                        if v___x_3537_ == 0 {
                            crate::leanh::lean_dec(v_a_3523_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_3525_);
                            v___x_3538_ = lean_array_get_size(v_decls_3510_);
                            v___x_3539_ = lean_mk_empty_array_with_capacity(v___x_3538_);
                            crate::leanh::lean_inc_ref(v_decls_3510_);
                            v___x_3540_ = l_Lean_Compiler_LCNF_mkFixedParamsMap(v_decls_3510_);
                            v___x_3541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v___x_3538_, v_decls_3510_, v_alreadySpecialized_3512_, v___x_3540_, v_a_3523_, v___x_3518_, v___x_3539_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
                            crate::leanh::lean_dec(v_a_3523_);
                            crate::leanh::lean_dec(v___x_3540_);
                            crate::leanh::lean_dec_ref(v_decls_3510_);
                            return v___x_3541_;
                        }
                    }
                }
            }
            2 => {
                v___x_3528_ = lean_array_get_size(v_decls_3510_);
                v___x_3529_ = lean_mk_empty_array_with_capacity(v___x_3528_);
                v___x_3530_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_3512_, v_decls_3510_, v___x_3528_, v___x_3518_, v___x_3529_);
                crate::leanh::lean_dec_ref(v_decls_3510_);
                if v_isShared_3526_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3525_, 0, v___x_3530_);
                    v___x_3532_ = v___x_3525_;
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
            3 => {
                return v___x_3532_;
            }
            4 => {
                if v_isShared_3546_ == 0 {
                    v___x_3548_ = v___x_3545_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
                    v___x_3548_ = v_reuseFailAlloc_3549_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_computeSpecEntries___boxed(
    mut v_decls_3551_: *mut crate::leanh::LeanObject,
    mut v_autoSpecialize_3552_: *mut crate::leanh::LeanObject,
    mut v_alreadySpecialized_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Lean_Compiler_LCNF_computeSpecEntries(
        v_decls_3551_,
        v_autoSpecialize_3552_,
        v_alreadySpecialized_3553_,
        v_a_3554_,
        v_a_3555_,
        v_a_3556_,
        v_a_3557_,
    );
    crate::leanh::lean_dec(v_a_3557_);
    crate::leanh::lean_dec_ref(v_a_3556_);
    crate::leanh::lean_dec(v_a_3555_);
    crate::leanh::lean_dec_ref(v_a_3554_);
    crate::leanh::lean_dec_ref(v_alreadySpecialized_3553_);
    return v_res_3559_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(
    mut v_upperBound_3560_: *mut crate::leanh::LeanObject,
    mut v___x_3561_: *mut crate::leanh::LeanObject,
    mut v_autoSpecialize_3562_: *mut crate::leanh::LeanObject,
    mut v___x_3563_: *mut crate::leanh::LeanObject,
    mut v___x_3564_: *mut crate::leanh::LeanObject,
    mut v_inst_3565_: *mut crate::leanh::LeanObject,
    mut v_R_3566_: *mut crate::leanh::LeanObject,
    mut v_a_3567_: *mut crate::leanh::LeanObject,
    mut v_b_3568_: *mut crate::leanh::LeanObject,
    mut v_c_3569_: *mut crate::leanh::LeanObject,
    mut v___y_3570_: *mut crate::leanh::LeanObject,
    mut v___y_3571_: *mut crate::leanh::LeanObject,
    mut v___y_3572_: *mut crate::leanh::LeanObject,
    mut v___y_3573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3575_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v_upperBound_3560_, v___x_3561_, v_autoSpecialize_3562_, v___x_3563_, v___x_3564_, v_a_3567_, v_b_3568_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
    return v___x_3575_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___boxed(
    mut v_upperBound_3576_: *mut crate::leanh::LeanObject,
    mut v___x_3577_: *mut crate::leanh::LeanObject,
    mut v_autoSpecialize_3578_: *mut crate::leanh::LeanObject,
    mut v___x_3579_: *mut crate::leanh::LeanObject,
    mut v___x_3580_: *mut crate::leanh::LeanObject,
    mut v_inst_3581_: *mut crate::leanh::LeanObject,
    mut v_R_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
    mut v_b_3584_: *mut crate::leanh::LeanObject,
    mut v_c_3585_: *mut crate::leanh::LeanObject,
    mut v___y_3586_: *mut crate::leanh::LeanObject,
    mut v___y_3587_: *mut crate::leanh::LeanObject,
    mut v___y_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3591_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(
            v_upperBound_3576_,
            v___x_3577_,
            v_autoSpecialize_3578_,
            v___x_3579_,
            v___x_3580_,
            v_inst_3581_,
            v_R_3582_,
            v_a_3583_,
            v_b_3584_,
            v_c_3585_,
            v___y_3586_,
            v___y_3587_,
            v___y_3588_,
            v___y_3589_,
        );
    crate::leanh::lean_dec(v___y_3589_);
    crate::leanh::lean_dec_ref(v___y_3588_);
    crate::leanh::lean_dec(v___y_3587_);
    crate::leanh::lean_dec_ref(v___y_3586_);
    crate::leanh::lean_dec_ref(v___x_3577_);
    crate::leanh::lean_dec(v_upperBound_3576_);
    return v_res_3591_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(
    mut v_alreadySpecialized_3592_: *mut crate::leanh::LeanObject,
    mut v_as_3593_: *mut crate::leanh::LeanObject,
    mut v_i_3594_: *mut crate::leanh::LeanObject,
    mut v_j_3595_: *mut crate::leanh::LeanObject,
    mut v_inv_3596_: *mut crate::leanh::LeanObject,
    mut v_bs_3597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ =
        l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(
            v_alreadySpecialized_3592_,
            v_as_3593_,
            v_i_3594_,
            v_j_3595_,
            v_bs_3597_,
        );
    return v___x_3598_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___boxed(
    mut v_alreadySpecialized_3599_: *mut crate::leanh::LeanObject,
    mut v_as_3600_: *mut crate::leanh::LeanObject,
    mut v_i_3601_: *mut crate::leanh::LeanObject,
    mut v_j_3602_: *mut crate::leanh::LeanObject,
    mut v_inv_3603_: *mut crate::leanh::LeanObject,
    mut v_bs_3604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3605_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(
        v_alreadySpecialized_3599_,
        v_as_3600_,
        v_i_3601_,
        v_j_3602_,
        v_inv_3603_,
        v_bs_3604_,
    );
    crate::leanh::lean_dec_ref(v_as_3600_);
    crate::leanh::lean_dec_ref(v_alreadySpecialized_3599_);
    return v_res_3605_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(
    mut v_upperBound_3606_: *mut crate::leanh::LeanObject,
    mut v___x_3607_: *mut crate::leanh::LeanObject,
    mut v_inst_3608_: *mut crate::leanh::LeanObject,
    mut v_R_3609_: *mut crate::leanh::LeanObject,
    mut v_a_3610_: *mut crate::leanh::LeanObject,
    mut v_b_3611_: *mut crate::leanh::LeanObject,
    mut v_c_3612_: *mut crate::leanh::LeanObject,
    mut v___y_3613_: *mut crate::leanh::LeanObject,
    mut v___y_3614_: *mut crate::leanh::LeanObject,
    mut v___y_3615_: *mut crate::leanh::LeanObject,
    mut v___y_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3618_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_3606_, v___x_3607_, v_a_3610_, v_b_3611_);
    return v___x_3618_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___boxed(
    mut v_upperBound_3619_: *mut crate::leanh::LeanObject,
    mut v___x_3620_: *mut crate::leanh::LeanObject,
    mut v_inst_3621_: *mut crate::leanh::LeanObject,
    mut v_R_3622_: *mut crate::leanh::LeanObject,
    mut v_a_3623_: *mut crate::leanh::LeanObject,
    mut v_b_3624_: *mut crate::leanh::LeanObject,
    mut v_c_3625_: *mut crate::leanh::LeanObject,
    mut v___y_3626_: *mut crate::leanh::LeanObject,
    mut v___y_3627_: *mut crate::leanh::LeanObject,
    mut v___y_3628_: *mut crate::leanh::LeanObject,
    mut v___y_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3631_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(
            v_upperBound_3619_,
            v___x_3620_,
            v_inst_3621_,
            v_R_3622_,
            v_a_3623_,
            v_b_3624_,
            v_c_3625_,
            v___y_3626_,
            v___y_3627_,
            v___y_3628_,
            v___y_3629_,
        );
    crate::leanh::lean_dec(v___y_3629_);
    crate::leanh::lean_dec_ref(v___y_3628_);
    crate::leanh::lean_dec(v___y_3627_);
    crate::leanh::lean_dec_ref(v___y_3626_);
    crate::leanh::lean_dec_ref(v___x_3620_);
    crate::leanh::lean_dec(v_upperBound_3619_);
    return v_res_3631_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(
    mut v_upperBound_3632_: *mut crate::leanh::LeanObject,
    mut v_decls_3633_: *mut crate::leanh::LeanObject,
    mut v_alreadySpecialized_3634_: *mut crate::leanh::LeanObject,
    mut v___x_3635_: *mut crate::leanh::LeanObject,
    mut v_a_3636_: *mut crate::leanh::LeanObject,
    mut v_inst_3637_: *mut crate::leanh::LeanObject,
    mut v_R_3638_: *mut crate::leanh::LeanObject,
    mut v_a_3639_: *mut crate::leanh::LeanObject,
    mut v_b_3640_: *mut crate::leanh::LeanObject,
    mut v_c_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
    mut v___y_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3647_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_3632_, v_decls_3633_, v_alreadySpecialized_3634_, v___x_3635_, v_a_3636_, v_a_3639_, v_b_3640_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
    return v___x_3647_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___boxed(
    mut v_upperBound_3648_: *mut crate::leanh::LeanObject,
    mut v_decls_3649_: *mut crate::leanh::LeanObject,
    mut v_alreadySpecialized_3650_: *mut crate::leanh::LeanObject,
    mut v___x_3651_: *mut crate::leanh::LeanObject,
    mut v_a_3652_: *mut crate::leanh::LeanObject,
    mut v_inst_3653_: *mut crate::leanh::LeanObject,
    mut v_R_3654_: *mut crate::leanh::LeanObject,
    mut v_a_3655_: *mut crate::leanh::LeanObject,
    mut v_b_3656_: *mut crate::leanh::LeanObject,
    mut v_c_3657_: *mut crate::leanh::LeanObject,
    mut v___y_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
    mut v___y_3660_: *mut crate::leanh::LeanObject,
    mut v___y_3661_: *mut crate::leanh::LeanObject,
    mut v___y_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3663_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(
            v_upperBound_3648_,
            v_decls_3649_,
            v_alreadySpecialized_3650_,
            v___x_3651_,
            v_a_3652_,
            v_inst_3653_,
            v_R_3654_,
            v_a_3655_,
            v_b_3656_,
            v_c_3657_,
            v___y_3658_,
            v___y_3659_,
            v___y_3660_,
            v___y_3661_,
        );
    crate::leanh::lean_dec(v___y_3661_);
    crate::leanh::lean_dec_ref(v___y_3660_);
    crate::leanh::lean_dec(v___y_3659_);
    crate::leanh::lean_dec_ref(v___y_3658_);
    crate::leanh::lean_dec_ref(v_a_3652_);
    crate::leanh::lean_dec(v___x_3651_);
    crate::leanh::lean_dec_ref(v_alreadySpecialized_3650_);
    crate::leanh::lean_dec_ref(v_decls_3649_);
    crate::leanh::lean_dec(v_upperBound_3648_);
    return v_res_3663_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3664_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3664_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0,
    );
    v___x_3666_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3666_, 0, v___x_3665_);
    return v___x_3666_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3667_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1,
    );
    v___x_3668_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3669_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3669_, 0, v___x_3668_);
    crate::leanh::lean_ctor_set(v___x_3669_, 1, v___x_3668_);
    crate::leanh::lean_ctor_set(v___x_3669_, 2, v___x_3668_);
    crate::leanh::lean_ctor_set(v___x_3669_, 3, v___x_3668_);
    crate::leanh::lean_ctor_set(v___x_3669_, 4, v___x_3667_);
    crate::leanh::lean_ctor_set(v___x_3669_, 5, v___x_3667_);
    crate::leanh::lean_ctor_set(v___x_3669_, 6, v___x_3667_);
    crate::leanh::lean_ctor_set(v___x_3669_, 7, v___x_3667_);
    crate::leanh::lean_ctor_set(v___x_3669_, 8, v___x_3667_);
    crate::leanh::lean_ctor_set(v___x_3669_, 9, v___x_3667_);
    return v___x_3669_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3()
-> f64 {
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: f64 = 0.0;
    v___x_3670_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3671_ = lean_float_of_nat(v___x_3670_);
    return v___x_3671_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(
    mut v_cls_3675_: *mut crate::leanh::LeanObject,
    mut v_msg_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
    mut v___y_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v_env_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3709_: u8 = 0;
    let mut v_tid_3710_: u64 = 0;
    let mut v_traces_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3715_: u8 = 0;
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: f64 = 0.0;
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3741_: u8 = 0;
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v_unused_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v_a_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3682_ = crate::leanh::lean_ctor_get(v___y_3679_, 2);
                v_ref_3683_ = crate::leanh::lean_ctor_get(v___y_3679_, 5);
                v___x_3684_ = lean_st_ref_get(v___y_3680_);
                v___x_3685_ = lean_st_ref_get(v___y_3678_);
                v___x_3686_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3677_);
                if crate::leanh::lean_obj_tag(v___x_3686_) == 0 {
                    v_a_3687_ = crate::leanh::lean_ctor_get(v___x_3686_, 0);
                    v_isSharedCheck_3745_ = (!crate::leanh::lean_is_exclusive(v___x_3686_)) as u8;
                    if v_isSharedCheck_3745_ == 0 {
                        v___x_3689_ = v___x_3686_;
                        v_isShared_3690_ = v_isSharedCheck_3745_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3687_);
                        crate::leanh::lean_dec(v___x_3686_);
                        v___x_3689_ = crate::leanh::lean_box(0);
                        v_isShared_3690_ = v_isSharedCheck_3745_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3685_);
                    crate::leanh::lean_dec(v___x_3684_);
                    crate::leanh::lean_dec_ref(v_msg_3676_);
                    crate::leanh::lean_dec(v_cls_3675_);
                    v_a_3746_ = crate::leanh::lean_ctor_get(v___x_3686_, 0);
                    v_isSharedCheck_3753_ = (!crate::leanh::lean_is_exclusive(v___x_3686_)) as u8;
                    if v_isSharedCheck_3753_ == 0 {
                        v___x_3748_ = v___x_3686_;
                        v_isShared_3749_ = v_isSharedCheck_3753_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3746_);
                        crate::leanh::lean_dec(v___x_3686_);
                        v___x_3748_ = crate::leanh::lean_box(0);
                        v_isShared_3749_ = v_isSharedCheck_3753_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3691_ = crate::leanh::lean_ctor_get(v___x_3684_, 0);
                crate::leanh::lean_inc_ref(v_env_3691_);
                crate::leanh::lean_dec(v___x_3684_);
                v_lctx_3692_ = crate::leanh::lean_ctor_get(v___x_3685_, 0);
                v_isSharedCheck_3743_ = (!crate::leanh::lean_is_exclusive(v___x_3685_)) as u8;
                if v_isSharedCheck_3743_ == 0 {
                    v_unused_3744_ = crate::leanh::lean_ctor_get(v___x_3685_, 1);
                    crate::leanh::lean_dec(v_unused_3744_);
                    v___x_3694_ = v___x_3685_;
                    v_isShared_3695_ = v_isSharedCheck_3743_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_3692_);
                    crate::leanh::lean_dec(v___x_3685_);
                    v___x_3694_ = crate::leanh::lean_box(0);
                    v_isShared_3695_ = v_isSharedCheck_3743_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3696_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2);
                v___x_3697_ = lean_st_ref_take(v___y_3680_);
                v_traceState_3698_ = crate::leanh::lean_ctor_get(v___x_3697_, 4);
                v_env_3699_ = crate::leanh::lean_ctor_get(v___x_3697_, 0);
                v_nextMacroScope_3700_ = crate::leanh::lean_ctor_get(v___x_3697_, 1);
                v_ngen_3701_ = crate::leanh::lean_ctor_get(v___x_3697_, 2);
                v_auxDeclNGen_3702_ = crate::leanh::lean_ctor_get(v___x_3697_, 3);
                v_cache_3703_ = crate::leanh::lean_ctor_get(v___x_3697_, 5);
                v_messages_3704_ = crate::leanh::lean_ctor_get(v___x_3697_, 6);
                v_infoState_3705_ = crate::leanh::lean_ctor_get(v___x_3697_, 7);
                v_snapshotTasks_3706_ = crate::leanh::lean_ctor_get(v___x_3697_, 8);
                v_isSharedCheck_3742_ = (!crate::leanh::lean_is_exclusive(v___x_3697_)) as u8;
                if v_isSharedCheck_3742_ == 0 {
                    v___x_3708_ = v___x_3697_;
                    v_isShared_3709_ = v_isSharedCheck_3742_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3706_);
                    crate::leanh::lean_inc(v_infoState_3705_);
                    crate::leanh::lean_inc(v_messages_3704_);
                    crate::leanh::lean_inc(v_cache_3703_);
                    crate::leanh::lean_inc(v_traceState_3698_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3702_);
                    crate::leanh::lean_inc(v_ngen_3701_);
                    crate::leanh::lean_inc(v_nextMacroScope_3700_);
                    crate::leanh::lean_inc(v_env_3699_);
                    crate::leanh::lean_dec(v___x_3697_);
                    v___x_3708_ = crate::leanh::lean_box(0);
                    v_isShared_3709_ = v_isSharedCheck_3742_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_3710_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3698_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3711_ = crate::leanh::lean_ctor_get(v_traceState_3698_, 0);
                v_isSharedCheck_3741_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3698_)) as u8;
                if v_isSharedCheck_3741_ == 0 {
                    v___x_3713_ = v_traceState_3698_;
                    v_isShared_3714_ = v_isSharedCheck_3741_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3711_);
                    crate::leanh::lean_dec(v_traceState_3698_);
                    v___x_3713_ = crate::leanh::lean_box(0);
                    v_isShared_3714_ = v_isSharedCheck_3741_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3715_ = (crate::leanh::lean_unbox(v_a_3687_) as u8);
                crate::leanh::lean_dec(v_a_3687_);
                v___x_3716_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3692_, v___x_3715_);
                crate::leanh::lean_dec_ref(v_lctx_3692_);
                crate::leanh::lean_inc_ref(v_options_3682_);
                v___x_3717_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3717_, 0, v_env_3691_);
                crate::leanh::lean_ctor_set(v___x_3717_, 1, v___x_3696_);
                crate::leanh::lean_ctor_set(v___x_3717_, 2, v___x_3716_);
                crate::leanh::lean_ctor_set(v___x_3717_, 3, v_options_3682_);
                if v_isShared_3695_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3694_, 3);
                    crate::leanh::lean_ctor_set(v___x_3694_, 1, v_msg_3676_);
                    crate::leanh::lean_ctor_set(v___x_3694_, 0, v___x_3717_);
                    v___x_3719_ = v___x_3694_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3740_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_msg_3676_);
                    v___x_3719_ = v_reuseFailAlloc_3740_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3720_ = crate::leanh::lean_box(0);
                v___x_3721_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3);
                v___x_3722_ = 0;
                v___x_3723_ =
                    l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4;
                v___x_3724_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3724_, 0, v_cls_3675_);
                crate::leanh::lean_ctor_set(v___x_3724_, 1, v___x_3720_);
                crate::leanh::lean_ctor_set(v___x_3724_, 2, v___x_3723_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3724_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3721_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3724_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3721_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3724_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3722_,
                );
                v___x_3725_ =
                    l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5;
                v___x_3726_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3726_, 0, v___x_3724_);
                crate::leanh::lean_ctor_set(v___x_3726_, 1, v___x_3719_);
                crate::leanh::lean_ctor_set(v___x_3726_, 2, v___x_3725_);
                crate::leanh::lean_inc(v_ref_3683_);
                v___x_3727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3727_, 0, v_ref_3683_);
                crate::leanh::lean_ctor_set(v___x_3727_, 1, v___x_3726_);
                v___x_3728_ = l_Lean_PersistentArray_push___redArg(v_traces_3711_, v___x_3727_);
                if v_isShared_3714_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3713_, 0, v___x_3728_);
                    v___x_3730_ = v___x_3713_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3739_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3728_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3739_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3710_,
                    );
                    v___x_3730_ = v_reuseFailAlloc_3739_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3708_, 4, v___x_3730_);
                    v___x_3732_ = v___x_3708_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3738_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_env_3699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_nextMacroScope_3700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 2, v_ngen_3701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 3, v_auxDeclNGen_3702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 4, v___x_3730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 5, v_cache_3703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 6, v_messages_3704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 7, v_infoState_3705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 8, v_snapshotTasks_3706_);
                    v___x_3732_ = v_reuseFailAlloc_3738_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3733_ = lean_st_ref_set(v___y_3680_, v___x_3732_);
                v___x_3734_ = crate::leanh::lean_box(0);
                if v_isShared_3690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3689_, 0, v___x_3734_);
                    v___x_3736_ = v___x_3689_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
                    v___x_3736_ = v_reuseFailAlloc_3737_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3736_;
            }
            9 => {
                if v_isShared_3749_ == 0 {
                    v___x_3751_ = v___x_3748_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3752_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
                    v___x_3751_ = v_reuseFailAlloc_3752_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___boxed(
    mut v_cls_3754_: *mut crate::leanh::LeanObject,
    mut v_msg_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
    mut v___y_3760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3761_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(
        v_cls_3754_,
        v_msg_3755_,
        v___y_3756_,
        v___y_3757_,
        v___y_3758_,
        v___y_3759_,
    );
    crate::leanh::lean_dec(v___y_3759_);
    crate::leanh::lean_dec_ref(v___y_3758_);
    crate::leanh::lean_dec(v___y_3757_);
    crate::leanh::lean_dec_ref(v___y_3756_);
    return v_res_3761_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(
    mut v_xs_3762_: *mut crate::leanh::LeanObject,
    mut v_ys_3763_: *mut crate::leanh::LeanObject,
    mut v_x_3764_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3766_: u8 = 0;
    let mut v_one_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3765_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3766_ = lean_nat_dec_eq(v_x_3764_, v_zero_3765_);
                if v_isZero_3766_ == 1 {
                    crate::leanh::lean_dec(v_x_3764_);
                    return v_isZero_3766_;
                } else {
                    v_one_3767_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3768_ = lean_nat_sub(v_x_3764_, v_one_3767_);
                    crate::leanh::lean_dec(v_x_3764_);
                    v___x_3769_ = lean_array_fget_borrowed(v_xs_3762_, v_n_3768_);
                    v___x_3770_ = lean_array_fget_borrowed(v_ys_3763_, v_n_3768_);
                    v___x_3771_ = lean_nat_dec_eq(v___x_3769_, v___x_3770_);
                    if v___x_3771_ == 0 {
                        crate::leanh::lean_dec(v_n_3768_);
                        return v___x_3771_;
                    } else {
                        v_x_3764_ = v_n_3768_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg___boxed(
    mut v_xs_3773_: *mut crate::leanh::LeanObject,
    mut v_ys_3774_: *mut crate::leanh::LeanObject,
    mut v_x_3775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3776_: u8 = 0;
    let mut v_r_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3776_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_3773_, v_ys_3774_, v_x_3775_);
    crate::leanh::lean_dec_ref(v_ys_3774_);
    crate::leanh::lean_dec_ref(v_xs_3773_);
    v_r_3777_ = crate::leanh::lean_box((v_res_3776_) as usize);
    return v_r_3777_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(
    mut v_x_3778_: *mut crate::leanh::LeanObject,
    mut v_x_3779_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3778_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_3779_) == 0 {
            let mut v___x_3780_: u8 = 0;
            v___x_3780_ = 1;
            return v___x_3780_;
        } else {
            let mut v___x_3781_: u8 = 0;
            v___x_3781_ = 0;
            return v___x_3781_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_3779_) == 0 {
            let mut v___x_3782_: u8 = 0;
            v___x_3782_ = 0;
            return v___x_3782_;
        } else {
            let mut v_val_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3787_: u8 = 0;
            v_val_3783_ = crate::leanh::lean_ctor_get(v_x_3778_, 0);
            v_val_3784_ = crate::leanh::lean_ctor_get(v_x_3779_, 0);
            v___x_3785_ = lean_array_get_size(v_val_3783_);
            v___x_3786_ = lean_array_get_size(v_val_3784_);
            v___x_3787_ = lean_nat_dec_eq(v___x_3785_, v___x_3786_);
            if v___x_3787_ == 0 {
                return v___x_3787_;
            } else {
                let mut v___x_3788_: u8 = 0;
                v___x_3788_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_val_3783_, v_val_3784_, v___x_3785_);
                return v___x_3788_;
            }
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0___boxed(
    mut v_x_3789_: *mut crate::leanh::LeanObject,
    mut v_x_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3791_: u8 = 0;
    let mut v_r_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(
        v_x_3789_, v_x_3790_,
    );
    crate::leanh::lean_dec(v_x_3790_);
    crate::leanh::lean_dec(v_x_3789_);
    v_r_3792_ = crate::leanh::lean_box((v_res_3791_) as usize);
    return v_r_3792_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(
    mut v_x_3795_: *mut crate::leanh::LeanObject,
    mut v_specArgs_x3f_3796_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: u8 = 0;
    v___x_3797_ = l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0;
    v___x_3798_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(
        v_specArgs_x3f_3796_,
        v___x_3797_,
    );
    return v___x_3798_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed(
    mut v_x_3799_: *mut crate::leanh::LeanObject,
    mut v_specArgs_x3f_3800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3801_: u8 = 0;
    let mut v_r_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3801_ = l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(v_x_3799_, v_specArgs_x3f_3800_);
    crate::leanh::lean_dec(v_specArgs_x3f_3800_);
    crate::leanh::lean_dec(v_x_3799_);
    v_r_3802_ = crate::leanh::lean_box((v_res_3801_) as usize);
    return v_r_3802_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(
    mut v_a_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___y_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weak_3817_: u8 = 0;
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3803_) == 0 {
                    v___x_3805_ = l_List_reverse___redArg(v_a_3804_);
                    return v___x_3805_;
                } else {
                    v_head_3806_ = crate::leanh::lean_ctor_get(v_a_3803_, 0);
                    v_tail_3807_ = crate::leanh::lean_ctor_get(v_a_3803_, 1);
                    v_isSharedCheck_3824_ = (!crate::leanh::lean_is_exclusive(v_a_3803_)) as u8;
                    if v_isSharedCheck_3824_ == 0 {
                        v___x_3809_ = v_a_3803_;
                        v_isShared_3810_ = v_isSharedCheck_3824_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3807_);
                        crate::leanh::lean_inc(v_head_3806_);
                        crate::leanh::lean_dec(v_a_3803_);
                        v___x_3809_ = crate::leanh::lean_box(0);
                        v_isShared_3810_ = v_isSharedCheck_3824_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_head_3806_) {
                0 => {
                    v_weak_3817_ = crate::leanh::lean_ctor_get_uint8(v_head_3806_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_head_3806_, 0);
                    if v_weak_3817_ == 0 {
                        v___x_3818_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
                        v___y_3812_ = v___x_3818_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3819_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
                        v___y_3812_ = v___x_3819_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v___x_3820_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8);
                    v___y_3812_ = v___x_3820_;
                    state = 2;
                    continue;
                }
                2 => {
                    v___x_3821_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11);
                    v___y_3812_ = v___x_3821_;
                    state = 2;
                    continue;
                }
                3 => {
                    v___x_3822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14);
                    v___y_3812_ = v___x_3822_;
                    state = 2;
                    continue;
                }
                _ => {
                    v___x_3823_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17);
                    v___y_3812_ = v___x_3823_;
                    state = 2;
                    continue;
                }
            },
            2 => {
                crate::leanh::lean_inc_ref(v___y_3812_);
                if v_isShared_3810_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3809_, 1, v_a_3804_);
                    crate::leanh::lean_ctor_set(v___x_3809_, 0, v___y_3812_);
                    v___x_3814_ = v___x_3809_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___y_3812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_a_3804_);
                    v___x_3814_ = v_reuseFailAlloc_3816_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_3803_ = v_tail_3807_;
                v_a_3804_ = v___x_3814_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3825_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3826_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0);
    v___x_3827_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3827_, 0, v___x_3826_);
    return v___x_3827_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1);
    v___x_3829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3829_, 0, v___x_3828_);
    crate::leanh::lean_ctor_set(v___x_3829_, 1, v___x_3828_);
    return v___x_3829_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5;
    v___x_3840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7;
    v___x_3841_ = l_Lean_Name_append(v___x_3840_, v___x_3839_);
    return v___x_3841_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9;
    v___x_3844_ = l_Lean_stringToMessageData(v___x_3843_);
    return v___x_3844_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(
    mut v_as_3845_: *mut crate::leanh::LeanObject,
    mut v_sz_3846_: usize,
    mut v_i_3847_: usize,
    mut v_b_3848_: *mut crate::leanh::LeanObject,
    mut v___y_3849_: *mut crate::leanh::LeanObject,
    mut v___y_3850_: *mut crate::leanh::LeanObject,
    mut v___y_3851_: *mut crate::leanh::LeanObject,
    mut v___y_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: usize = 0;
    let mut v___x_3857_: usize = 0;
    let mut v___x_3859_: u8 = 0;
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsInfo_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3889_: u8 = 0;
    let mut v_unused_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: u8 = 0;
    let mut v___x_3894_: usize = 0;
    let mut v___x_3895_: usize = 0;
    let mut v___x_3896_: u8 = 0;
    let mut v_options_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3898_: u8 = 0;
    let mut v_inheritedTraceOptions_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3859_ = lean_usize_dec_lt(v_i_3847_, v_sz_3846_);
                if v___x_3859_ == 0 {
                    v___x_3860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3860_, 0, v_b_3848_);
                    return v___x_3860_;
                } else {
                    v_a_3861_ = lean_array_uget_borrowed(v_as_3845_, v_i_3847_);
                    v_declName_3862_ = crate::leanh::lean_ctor_get(v_a_3861_, 0);
                    v_paramsInfo_3863_ = crate::leanh::lean_ctor_get(v_a_3861_, 1);
                    v___x_3864_ = crate::leanh::lean_box(0);
                    v___x_3891_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3892_ = lean_array_get_size(v_paramsInfo_3863_);
                    v___x_3893_ = lean_nat_dec_lt(v___x_3891_, v___x_3892_);
                    if v___x_3893_ == 0 {
                        v_a_3855_ = v___x_3864_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_3893_ == 0 {
                            v_a_3855_ = v___x_3864_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3894_ = 0usize;
                            v___x_3895_ = lean_usize_of_nat(v___x_3892_);
                            v___x_3896_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_paramsInfo_3863_, v___x_3894_, v___x_3895_);
                            if v___x_3896_ == 0 {
                                v_a_3855_ = v___x_3864_;
                                state = 1;
                                continue;
                            } else {
                                v_options_3897_ = crate::leanh::lean_ctor_get(v___y_3851_, 2);
                                v_hasTrace_3898_ = crate::leanh::lean_ctor_get_uint8(
                                    v_options_3897_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                );
                                if v_hasTrace_3898_ == 0 {
                                    v___y_3866_ = v___y_3852_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_inheritedTraceOptions_3899_ =
                                        crate::leanh::lean_ctor_get(v___y_3851_, 13);
                                    v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5;
                                    v___x_3901_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8);
                                    v___x_3902_ =
                                        l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                            v_inheritedTraceOptions_3899_,
                                            v_options_3897_,
                                            v___x_3901_,
                                        );
                                    if v___x_3902_ == 0 {
                                        v___y_3866_ = v___y_3852_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_declName_3862_);
                                        v___x_3903_ = l_Lean_MessageData_ofName(v_declName_3862_);
                                        v___x_3904_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10);
                                        v___x_3905_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3905_, 0, v___x_3903_);
                                        crate::leanh::lean_ctor_set(v___x_3905_, 1, v___x_3904_);
                                        crate::leanh::lean_inc_ref(v_paramsInfo_3863_);
                                        v___x_3906_ = lean_array_to_list(v_paramsInfo_3863_);
                                        v___x_3907_ = crate::leanh::lean_box(0);
                                        v___x_3908_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(v___x_3906_, v___x_3907_);
                                        v___x_3909_ = l_Lean_MessageData_ofList(v___x_3908_);
                                        v___x_3910_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3910_, 0, v___x_3905_);
                                        crate::leanh::lean_ctor_set(v___x_3910_, 1, v___x_3909_);
                                        v___x_3911_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v___x_3900_, v___x_3910_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
                                        if crate::leanh::lean_obj_tag(v___x_3911_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3911_, 1);
                                            v___y_3866_ = v___y_3852_;
                                            state = 2;
                                            continue;
                                        } else {
                                            return v___x_3911_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3856_ = 1usize;
                v___x_3857_ = lean_usize_add(v_i_3847_, v___x_3856_);
                v_i_3847_ = v___x_3857_;
                v_b_3848_ = v_a_3855_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3867_ = lean_st_ref_take(v___y_3866_);
                v_env_3868_ = crate::leanh::lean_ctor_get(v___x_3867_, 0);
                v_nextMacroScope_3869_ = crate::leanh::lean_ctor_get(v___x_3867_, 1);
                v_ngen_3870_ = crate::leanh::lean_ctor_get(v___x_3867_, 2);
                v_auxDeclNGen_3871_ = crate::leanh::lean_ctor_get(v___x_3867_, 3);
                v_traceState_3872_ = crate::leanh::lean_ctor_get(v___x_3867_, 4);
                v_messages_3873_ = crate::leanh::lean_ctor_get(v___x_3867_, 6);
                v_infoState_3874_ = crate::leanh::lean_ctor_get(v___x_3867_, 7);
                v_snapshotTasks_3875_ = crate::leanh::lean_ctor_get(v___x_3867_, 8);
                v_isSharedCheck_3889_ = (!crate::leanh::lean_is_exclusive(v___x_3867_)) as u8;
                if v_isSharedCheck_3889_ == 0 {
                    v_unused_3890_ = crate::leanh::lean_ctor_get(v___x_3867_, 5);
                    crate::leanh::lean_dec(v_unused_3890_);
                    v___x_3877_ = v___x_3867_;
                    v_isShared_3878_ = v_isSharedCheck_3889_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3875_);
                    crate::leanh::lean_inc(v_infoState_3874_);
                    crate::leanh::lean_inc(v_messages_3873_);
                    crate::leanh::lean_inc(v_traceState_3872_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3871_);
                    crate::leanh::lean_inc(v_ngen_3870_);
                    crate::leanh::lean_inc(v_nextMacroScope_3869_);
                    crate::leanh::lean_inc(v_env_3868_);
                    crate::leanh::lean_dec(v___x_3867_);
                    v___x_3877_ = crate::leanh::lean_box(0);
                    v_isShared_3878_ = v_isSharedCheck_3889_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3879_ = l_Lean_Compiler_LCNF_specExtension;
                v_toEnvExtension_3880_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                v_asyncMode_3881_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3880_, 2);
                v___x_3882_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_a_3861_);
                v___x_3883_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3879_,
                    v_env_3868_,
                    v_a_3861_,
                    v_asyncMode_3881_,
                    v___x_3882_,
                );
                v___x_3884_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2);
                if v_isShared_3878_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3877_, 5, v___x_3884_);
                    crate::leanh::lean_ctor_set(v___x_3877_, 0, v___x_3883_);
                    v___x_3886_ = v___x_3877_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_nextMacroScope_3869_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 2, v_ngen_3870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 3, v_auxDeclNGen_3871_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 4, v_traceState_3872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 5, v___x_3884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 6, v_messages_3873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 7, v_infoState_3874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 8, v_snapshotTasks_3875_);
                    v___x_3886_ = v_reuseFailAlloc_3888_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3887_ = lean_st_ref_set(v___y_3866_, v___x_3886_);
                v_a_3855_ = v___x_3864_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___boxed(
    mut v_as_3912_: *mut crate::leanh::LeanObject,
    mut v_sz_3913_: *mut crate::leanh::LeanObject,
    mut v_i_3914_: *mut crate::leanh::LeanObject,
    mut v_b_3915_: *mut crate::leanh::LeanObject,
    mut v___y_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
    mut v___y_3919_: *mut crate::leanh::LeanObject,
    mut v___y_3920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3921_: usize = 0;
    let mut v_i_boxed_3922_: usize = 0;
    let mut v_res_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3921_ = crate::leanh::lean_unbox_usize(v_sz_3913_);
    crate::leanh::lean_dec(v_sz_3913_);
    v_i_boxed_3922_ = crate::leanh::lean_unbox_usize(v_i_3914_);
    crate::leanh::lean_dec(v_i_3914_);
    v_res_3923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_as_3912_, v_sz_boxed_3921_, v_i_boxed_3922_, v_b_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
    crate::leanh::lean_dec(v___y_3919_);
    crate::leanh::lean_dec_ref(v___y_3918_);
    crate::leanh::lean_dec(v___y_3917_);
    crate::leanh::lean_dec_ref(v___y_3916_);
    crate::leanh::lean_dec_ref(v_as_3912_);
    return v_res_3923_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveSpecEntries(
    mut v_decls_3925_: *mut crate::leanh::LeanObject,
    mut v_a_3926_: *mut crate::leanh::LeanObject,
    mut v_a_3927_: *mut crate::leanh::LeanObject,
    mut v_a_3928_: *mut crate::leanh::LeanObject,
    mut v_a_3929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3939_: usize = 0;
    let mut v___x_3940_: usize = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3944_: u8 = 0;
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3948_: u8 = 0;
    let mut v_unused_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3953_: u8 = 0;
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3931_ = l_Lean_Compiler_LCNF_saveSpecEntries___closed__0;
                v___x_3932_ = lean_array_get_size(v_decls_3925_);
                v___x_3933_ = 0;
                v___x_3934_ = crate::leanh::lean_box((v___x_3933_) as usize);
                v___x_3935_ = lean_mk_array(v___x_3932_, v___x_3934_);
                v___x_3936_ = l_Lean_Compiler_LCNF_computeSpecEntries(
                    v_decls_3925_,
                    v___f_3931_,
                    v___x_3935_,
                    v_a_3926_,
                    v_a_3927_,
                    v_a_3928_,
                    v_a_3929_,
                );
                crate::leanh::lean_dec_ref(v___x_3935_);
                if crate::leanh::lean_obj_tag(v___x_3936_) == 0 {
                    v_a_3937_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                    crate::leanh::lean_inc(v_a_3937_);
                    crate::leanh::lean_dec_ref_known(v___x_3936_, 1);
                    v___x_3938_ = crate::leanh::lean_box(0);
                    v_sz_3939_ = lean_array_size(v_a_3937_);
                    v___x_3940_ = 0usize;
                    v___x_3941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_a_3937_, v_sz_3939_, v___x_3940_, v___x_3938_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
                    crate::leanh::lean_dec(v_a_3937_);
                    if crate::leanh::lean_obj_tag(v___x_3941_) == 0 {
                        v_isSharedCheck_3948_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3941_)) as u8;
                        if v_isSharedCheck_3948_ == 0 {
                            v_unused_3949_ = crate::leanh::lean_ctor_get(v___x_3941_, 0);
                            crate::leanh::lean_dec(v_unused_3949_);
                            v___x_3943_ = v___x_3941_;
                            v_isShared_3944_ = v_isSharedCheck_3948_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3941_);
                            v___x_3943_ = crate::leanh::lean_box(0);
                            v_isShared_3944_ = v_isSharedCheck_3948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3941_;
                    }
                } else {
                    v_a_3950_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                    v_isSharedCheck_3957_ = (!crate::leanh::lean_is_exclusive(v___x_3936_)) as u8;
                    if v_isSharedCheck_3957_ == 0 {
                        v___x_3952_ = v___x_3936_;
                        v_isShared_3953_ = v_isSharedCheck_3957_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3950_);
                        crate::leanh::lean_dec(v___x_3936_);
                        v___x_3952_ = crate::leanh::lean_box(0);
                        v_isShared_3953_ = v_isSharedCheck_3957_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3943_, 0, v___x_3938_);
                    v___x_3946_ = v___x_3943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3938_);
                    v___x_3946_ = v_reuseFailAlloc_3947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3946_;
            }
            3 => {
                if v_isShared_3953_ == 0 {
                    v___x_3955_ = v___x_3952_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
                    v___x_3955_ = v_reuseFailAlloc_3956_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_saveSpecEntries___boxed(
    mut v_decls_3958_: *mut crate::leanh::LeanObject,
    mut v_a_3959_: *mut crate::leanh::LeanObject,
    mut v_a_3960_: *mut crate::leanh::LeanObject,
    mut v_a_3961_: *mut crate::leanh::LeanObject,
    mut v_a_3962_: *mut crate::leanh::LeanObject,
    mut v_a_3963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3964_ = l_Lean_Compiler_LCNF_saveSpecEntries(
        v_decls_3958_,
        v_a_3959_,
        v_a_3960_,
        v_a_3961_,
        v_a_3962_,
    );
    crate::leanh::lean_dec(v_a_3962_);
    crate::leanh::lean_dec_ref(v_a_3961_);
    crate::leanh::lean_dec(v_a_3960_);
    crate::leanh::lean_dec_ref(v_a_3959_);
    return v_res_3964_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(
    mut v_xs_3965_: *mut crate::leanh::LeanObject,
    mut v_ys_3966_: *mut crate::leanh::LeanObject,
    mut v_hsz_3967_: *mut crate::leanh::LeanObject,
    mut v_x_3968_: *mut crate::leanh::LeanObject,
    mut v_x_3969_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3970_: u8 = 0;
    v___x_3970_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_3965_, v_ys_3966_, v_x_3968_);
    return v___x_3970_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___boxed(
    mut v_xs_3971_: *mut crate::leanh::LeanObject,
    mut v_ys_3972_: *mut crate::leanh::LeanObject,
    mut v_hsz_3973_: *mut crate::leanh::LeanObject,
    mut v_x_3974_: *mut crate::leanh::LeanObject,
    mut v_x_3975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3976_: u8 = 0;
    let mut v_r_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3976_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(v_xs_3971_, v_ys_3972_, v_hsz_3973_, v_x_3974_, v_x_3975_);
    crate::leanh::lean_dec_ref(v_ys_3972_);
    crate::leanh::lean_dec_ref(v_xs_3971_);
    v_r_3977_ = crate::leanh::lean_box((v_res_3976_) as usize);
    return v_r_3977_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(
    mut v_as_3978_: *mut crate::leanh::LeanObject,
    mut v_k_3979_: *mut crate::leanh::LeanObject,
    mut v_x_3980_: *mut crate::leanh::LeanObject,
    mut v_x_3981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: u8 = 0;
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: u8 = 0;
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: u8 = 0;
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3982_ = lean_nat_add(v_x_3980_, v_x_3981_);
                v___x_3983_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_3984_ = lean_nat_shiftr(v___x_3982_, v___x_3983_);
                crate::leanh::lean_dec(v___x_3982_);
                v_a_3985_ = lean_array_fget_borrowed(v_as_3978_, v_m_3984_);
                v___x_3986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_a_3985_, v_k_3979_);
                if v___x_3986_ == 0 {
                    crate::leanh::lean_dec(v_x_3981_);
                    v___x_3987_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_k_3979_, v_a_3985_);
                    if v___x_3987_ == 0 {
                        crate::leanh::lean_dec(v_m_3984_);
                        crate::leanh::lean_dec(v_x_3980_);
                        crate::leanh::lean_inc(v_a_3985_);
                        v___x_3988_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3988_, 0, v_a_3985_);
                        return v___x_3988_;
                    } else {
                        v___x_3989_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3990_ = lean_nat_dec_eq(v_m_3984_, v___x_3989_);
                        if v___x_3990_ == 0 {
                            v___x_3991_ = lean_nat_sub(v_m_3984_, v___x_3983_);
                            crate::leanh::lean_dec(v_m_3984_);
                            v___x_3992_ = lean_nat_dec_lt(v___x_3991_, v_x_3980_);
                            if v___x_3992_ == 0 {
                                v_x_3981_ = v___x_3991_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3991_);
                                crate::leanh::lean_dec(v_x_3980_);
                                v___x_3994_ = crate::leanh::lean_box(0);
                                return v___x_3994_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_3984_);
                            crate::leanh::lean_dec(v_x_3980_);
                            v___x_3995_ = crate::leanh::lean_box(0);
                            return v___x_3995_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3980_);
                    v___x_3996_ = lean_nat_add(v_m_3984_, v___x_3983_);
                    crate::leanh::lean_dec(v_m_3984_);
                    v___x_3997_ = lean_nat_dec_le(v___x_3996_, v_x_3981_);
                    if v___x_3997_ == 0 {
                        crate::leanh::lean_dec(v___x_3996_);
                        crate::leanh::lean_dec(v_x_3981_);
                        v___x_3998_ = crate::leanh::lean_box(0);
                        return v___x_3998_;
                    } else {
                        v_x_3980_ = v___x_3996_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg___boxed(
    mut v_as_4000_: *mut crate::leanh::LeanObject,
    mut v_k_4001_: *mut crate::leanh::LeanObject,
    mut v_x_4002_: *mut crate::leanh::LeanObject,
    mut v_x_4003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4004_ =
        l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(
            v_as_4000_, v_k_4001_, v_x_4002_, v_x_4003_,
        );
    crate::leanh::lean_dec_ref(v_k_4001_);
    crate::leanh::lean_dec_ref(v_as_4000_);
    return v_res_4004_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4005_: *mut crate::leanh::LeanObject,
    mut v_vals_4006_: *mut crate::leanh::LeanObject,
    mut v_i_4007_: *mut crate::leanh::LeanObject,
    mut v_k_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: u8 = 0;
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4009_ = lean_array_get_size(v_keys_4005_);
                v___x_4010_ = lean_nat_dec_lt(v_i_4007_, v___x_4009_);
                if v___x_4010_ == 0 {
                    crate::leanh::lean_dec(v_i_4007_);
                    v___x_4011_ = crate::leanh::lean_box(0);
                    return v___x_4011_;
                } else {
                    v_k_x27_4012_ = lean_array_fget_borrowed(v_keys_4005_, v_i_4007_);
                    v___x_4013_ = lean_name_eq(v_k_4008_, v_k_x27_4012_);
                    if v___x_4013_ == 0 {
                        v___x_4014_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4015_ = lean_nat_add(v_i_4007_, v___x_4014_);
                        crate::leanh::lean_dec(v_i_4007_);
                        v_i_4007_ = v___x_4015_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4017_ = lean_array_fget_borrowed(v_vals_4006_, v_i_4007_);
                        crate::leanh::lean_dec(v_i_4007_);
                        crate::leanh::lean_inc(v___x_4017_);
                        v___x_4018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4018_, 0, v___x_4017_);
                        return v___x_4018_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4019_: *mut crate::leanh::LeanObject,
    mut v_vals_4020_: *mut crate::leanh::LeanObject,
    mut v_i_4021_: *mut crate::leanh::LeanObject,
    mut v_k_4022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4019_, v_vals_4020_, v_i_4021_, v_k_4022_);
    crate::leanh::lean_dec(v_k_4022_);
    crate::leanh::lean_dec_ref(v_vals_4020_);
    crate::leanh::lean_dec_ref(v_keys_4019_);
    return v_res_4023_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(
    mut v_x_4024_: *mut crate::leanh::LeanObject,
    mut v_x_4025_: usize,
    mut v_x_4026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: usize = 0;
    let mut v___x_4030_: usize = 0;
    let mut v___x_4031_: usize = 0;
    let mut v_j_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: u8 = 0;
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: usize = 0;
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4024_) == 0 {
                    v_es_4027_ = crate::leanh::lean_ctor_get(v_x_4024_, 0);
                    v___x_4028_ = crate::leanh::lean_box(2);
                    v___x_4029_ = 5usize;
                    v___x_4030_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1);
                    v___x_4031_ = lean_usize_land(v_x_4025_, v___x_4030_);
                    v_j_4032_ = lean_usize_to_nat(v___x_4031_);
                    v___x_4033_ = lean_array_get_borrowed(v___x_4028_, v_es_4027_, v_j_4032_);
                    crate::leanh::lean_dec(v_j_4032_);
                    match crate::leanh::lean_obj_tag(v___x_4033_) {
                        0 => {
                            v_key_4034_ = crate::leanh::lean_ctor_get(v___x_4033_, 0);
                            v_val_4035_ = crate::leanh::lean_ctor_get(v___x_4033_, 1);
                            v___x_4036_ = lean_name_eq(v_x_4026_, v_key_4034_);
                            if v___x_4036_ == 0 {
                                v___x_4037_ = crate::leanh::lean_box(0);
                                return v___x_4037_;
                            } else {
                                crate::leanh::lean_inc(v_val_4035_);
                                v___x_4038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4038_, 0, v_val_4035_);
                                return v___x_4038_;
                            }
                        }
                        1 => {
                            v_node_4039_ = crate::leanh::lean_ctor_get(v___x_4033_, 0);
                            v___x_4040_ = lean_usize_shift_right(v_x_4025_, v___x_4029_);
                            v_x_4024_ = v_node_4039_;
                            v_x_4025_ = v___x_4040_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4042_ = crate::leanh::lean_box(0);
                            return v___x_4042_;
                        }
                    }
                } else {
                    v_ks_4043_ = crate::leanh::lean_ctor_get(v_x_4024_, 0);
                    v_vs_4044_ = crate::leanh::lean_ctor_get(v_x_4024_, 1);
                    v___x_4045_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4046_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4043_, v_vs_4044_, v___x_4045_, v_x_4026_);
                    return v___x_4046_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4047_: *mut crate::leanh::LeanObject,
    mut v_x_4048_: *mut crate::leanh::LeanObject,
    mut v_x_4049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_413__boxed_4050_: usize = 0;
    let mut v_res_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_413__boxed_4050_ = crate::leanh::lean_unbox_usize(v_x_4048_);
    crate::leanh::lean_dec(v_x_4048_);
    v_res_4051_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_4047_, v_x_413__boxed_4050_, v_x_4049_);
    crate::leanh::lean_dec(v_x_4049_);
    crate::leanh::lean_dec_ref(v_x_4047_);
    return v_res_4051_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(
    mut v_x_4052_: *mut crate::leanh::LeanObject,
    mut v_x_4053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4055_: u64 = 0;
    let mut v___x_4056_: usize = 0;
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: u64 = 0;
    let mut v_hash_4059_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4053_) == 0 {
                    v___x_4058_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4055_ = v___x_4058_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4059_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4053_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4055_ = v_hash_4059_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4056_ = lean_uint64_to_usize(v___y_4055_);
                v___x_4057_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_4052_, v___x_4056_, v_x_4053_);
                return v___x_4057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg___boxed(
    mut v_x_4060_: *mut crate::leanh::LeanObject,
    mut v_x_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4062_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_4060_, v_x_4061_);
    crate::leanh::lean_dec(v_x_4061_);
    crate::leanh::lean_dec_ref(v_x_4060_);
    return v_res_4062_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
    v___x_4064_ = crate::leanh::lean_box(0);
    v___x_4065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4065_, 0, v___x_4064_);
    crate::leanh::lean_ctor_set(v___x_4065_, 1, v___x_4063_);
    return v___x_4065_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(
    mut v_env_4066_: *mut crate::leanh::LeanObject,
    mut v_declName_4067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: u8 = 0;
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4068_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0_once
                    ),
                    _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0,
                );
                v___x_4069_ = l_Lean_Compiler_LCNF_specExtension;
                v___x_4077_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4066_, v_declName_4067_);
                if crate::leanh::lean_obj_tag(v___x_4077_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_4078_ = crate::leanh::lean_ctor_get(v___x_4077_, 0);
                    crate::leanh::lean_inc(v_val_4078_);
                    crate::leanh::lean_dec_ref_known(v___x_4077_, 1);
                    v___x_4092_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_4068_, v___x_4069_, v_env_4066_, v_val_4078_);
                    v___x_4093_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4094_ = lean_array_get_size(v___x_4092_);
                    v___x_4095_ = lean_nat_dec_lt(v___x_4093_, v___x_4094_);
                    if v___x_4095_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4092_);
                        state = 2;
                        continue;
                    } else {
                        v___x_4096_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4097_ = lean_nat_sub(v___x_4094_, v___x_4096_);
                        v___x_4098_ = lean_nat_dec_le(v___x_4093_, v___x_4097_);
                        if v___x_4098_ == 0 {
                            crate::leanh::lean_dec(v___x_4097_);
                            crate::leanh::lean_dec_ref(v___x_4092_);
                            state = 2;
                            continue;
                        } else {
                            v___x_4099_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
                            v___x_4100_ = 0;
                            crate::leanh::lean_inc(v_declName_4067_);
                            v___x_4101_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_4101_, 0, v_declName_4067_);
                            crate::leanh::lean_ctor_set(v___x_4101_, 1, v___x_4099_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_4101_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v___x_4100_,
                            );
                            v___x_4102_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_4092_, v___x_4101_, v___x_4093_, v___x_4097_);
                            crate::leanh::lean_dec_ref_known(v___x_4101_, 2);
                            crate::leanh::lean_dec_ref(v___x_4092_);
                            if crate::leanh::lean_obj_tag(v___x_4102_) == 0 {
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_4078_);
                                crate::leanh::lean_dec(v_declName_4067_);
                                crate::leanh::lean_dec_ref(v_env_4066_);
                                return v___x_4102_;
                            }
                        }
                    }
                }
            }
            1 => {
                v_toEnvExtension_4071_ = crate::leanh::lean_ctor_get(v___x_4069_, 0);
                v_asyncMode_4072_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4071_, 2);
                v___x_4073_ = crate::leanh::lean_box(0);
                v___x_4074_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_4068_,
                    v___x_4069_,
                    v_env_4066_,
                    v_asyncMode_4072_,
                    v___x_4073_,
                );
                v_snd_4075_ = crate::leanh::lean_ctor_get(v___x_4074_, 1);
                crate::leanh::lean_inc(v_snd_4075_);
                crate::leanh::lean_dec(v___x_4074_);
                v___x_4076_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_snd_4075_, v_declName_4067_);
                crate::leanh::lean_dec(v_declName_4067_);
                crate::leanh::lean_dec(v_snd_4075_);
                return v___x_4076_;
            }
            2 => {
                v___x_4080_ = 0;
                v___x_4081_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                    v___x_4068_,
                    v___x_4069_,
                    v_env_4066_,
                    v_val_4078_,
                    v___x_4080_,
                );
                crate::leanh::lean_dec(v_val_4078_);
                v___x_4082_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4083_ = lean_array_get_size(v___x_4081_);
                v___x_4084_ = lean_nat_dec_lt(v___x_4082_, v___x_4083_);
                if v___x_4084_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4081_);
                    state = 1;
                    continue;
                } else {
                    v___x_4085_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4086_ = lean_nat_sub(v___x_4083_, v___x_4085_);
                    v___x_4087_ = lean_nat_dec_le(v___x_4082_, v___x_4086_);
                    if v___x_4087_ == 0 {
                        crate::leanh::lean_dec(v___x_4086_);
                        crate::leanh::lean_dec_ref(v___x_4081_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4088_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
                        v___x_4089_ = 0;
                        crate::leanh::lean_inc(v_declName_4067_);
                        v___x_4090_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_4090_, 0, v_declName_4067_);
                        crate::leanh::lean_ctor_set(v___x_4090_, 1, v___x_4088_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_4090_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_4089_,
                        );
                        v___x_4091_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_4081_, v___x_4090_, v___x_4082_, v___x_4086_);
                        crate::leanh::lean_dec_ref_known(v___x_4090_, 2);
                        crate::leanh::lean_dec_ref(v___x_4081_);
                        if crate::leanh::lean_obj_tag(v___x_4091_) == 0 {
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_declName_4067_);
                            crate::leanh::lean_dec_ref(v_env_4066_);
                            return v___x_4091_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(
    mut v_00_u03b2_4103_: *mut crate::leanh::LeanObject,
    mut v_x_4104_: *mut crate::leanh::LeanObject,
    mut v_x_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4106_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_4104_, v_x_4105_);
    return v___x_4106_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___boxed(
    mut v_00_u03b2_4107_: *mut crate::leanh::LeanObject,
    mut v_x_4108_: *mut crate::leanh::LeanObject,
    mut v_x_4109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4110_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(
            v_00_u03b2_4107_,
            v_x_4108_,
            v_x_4109_,
        );
    crate::leanh::lean_dec(v_x_4109_);
    crate::leanh::lean_dec_ref(v_x_4108_);
    return v_res_4110_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(
    mut v_as_4111_: *mut crate::leanh::LeanObject,
    mut v_k_4112_: *mut crate::leanh::LeanObject,
    mut v_x_4113_: *mut crate::leanh::LeanObject,
    mut v_x_4114_: *mut crate::leanh::LeanObject,
    mut v_x_4115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4116_ =
        l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(
            v_as_4111_, v_k_4112_, v_x_4113_, v_x_4114_,
        );
    return v___x_4116_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___boxed(
    mut v_as_4117_: *mut crate::leanh::LeanObject,
    mut v_k_4118_: *mut crate::leanh::LeanObject,
    mut v_x_4119_: *mut crate::leanh::LeanObject,
    mut v_x_4120_: *mut crate::leanh::LeanObject,
    mut v_x_4121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4122_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(
        v_as_4117_, v_k_4118_, v_x_4119_, v_x_4120_, v_x_4121_,
    );
    crate::leanh::lean_dec_ref(v_k_4118_);
    crate::leanh::lean_dec_ref(v_as_4117_);
    return v_res_4122_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(
    mut v_00_u03b2_4123_: *mut crate::leanh::LeanObject,
    mut v_x_4124_: *mut crate::leanh::LeanObject,
    mut v_x_4125_: usize,
    mut v_x_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_4124_, v_x_4125_, v_x_4126_);
    return v___x_4127_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4128_: *mut crate::leanh::LeanObject,
    mut v_x_4129_: *mut crate::leanh::LeanObject,
    mut v_x_4130_: *mut crate::leanh::LeanObject,
    mut v_x_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_579__boxed_4132_: usize = 0;
    let mut v_res_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_579__boxed_4132_ = crate::leanh::lean_unbox_usize(v_x_4130_);
    crate::leanh::lean_dec(v_x_4130_);
    v_res_4133_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(v_00_u03b2_4128_, v_x_4129_, v_x_579__boxed_4132_, v_x_4131_);
    crate::leanh::lean_dec(v_x_4131_);
    crate::leanh::lean_dec_ref(v_x_4129_);
    return v_res_4133_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4134_: *mut crate::leanh::LeanObject,
    mut v_keys_4135_: *mut crate::leanh::LeanObject,
    mut v_vals_4136_: *mut crate::leanh::LeanObject,
    mut v_heq_4137_: *mut crate::leanh::LeanObject,
    mut v_i_4138_: *mut crate::leanh::LeanObject,
    mut v_k_4139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4135_, v_vals_4136_, v_i_4138_, v_k_4139_);
    return v___x_4140_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4141_: *mut crate::leanh::LeanObject,
    mut v_keys_4142_: *mut crate::leanh::LeanObject,
    mut v_vals_4143_: *mut crate::leanh::LeanObject,
    mut v_heq_4144_: *mut crate::leanh::LeanObject,
    mut v_i_4145_: *mut crate::leanh::LeanObject,
    mut v_k_4146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4147_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4141_, v_keys_4142_, v_vals_4143_, v_heq_4144_, v_i_4145_, v_k_4146_);
    crate::leanh::lean_dec(v_k_4146_);
    crate::leanh::lean_dec_ref(v_vals_4143_);
    crate::leanh::lean_dec_ref(v_keys_4142_);
    return v_res_4147_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0(
    mut v_declName_4148_: *mut crate::leanh::LeanObject,
    mut v_toPure_4149_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4151_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_4150_, v_declName_4148_);
    v___x_4152_ =
        crate::leanh::lean_apply_2(v_toPure_4149_, crate::leanh::lean_box(0), v___x_4151_);
    return v___x_4152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(
    mut v_inst_4153_: *mut crate::leanh::LeanObject,
    mut v_inst_4154_: *mut crate::leanh::LeanObject,
    mut v_declName_4155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4156_ = crate::leanh::lean_ctor_get(v_inst_4153_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4156_);
    v_toBind_4157_ = crate::leanh::lean_ctor_get(v_inst_4153_, 1);
    crate::leanh::lean_inc(v_toBind_4157_);
    crate::leanh::lean_dec_ref(v_inst_4153_);
    v_getEnv_4158_ = crate::leanh::lean_ctor_get(v_inst_4154_, 0);
    crate::leanh::lean_inc(v_getEnv_4158_);
    crate::leanh::lean_dec_ref(v_inst_4154_);
    v_toPure_4159_ = crate::leanh::lean_ctor_get(v_toApplicative_4156_, 1);
    crate::leanh::lean_inc(v_toPure_4159_);
    crate::leanh::lean_dec_ref(v_toApplicative_4156_);
    v___f_4160_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4160_, 0, v_declName_4155_);
    crate::leanh::lean_closure_set(v___f_4160_, 1, v_toPure_4159_);
    v___x_4161_ = crate::leanh::lean_apply_4(
        v_toBind_4157_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_4158_,
        v___f_4160_,
    );
    return v___x_4161_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSpecEntry_x3f(
    mut v_m_4162_: *mut crate::leanh::LeanObject,
    mut v_inst_4163_: *mut crate::leanh::LeanObject,
    mut v_inst_4164_: *mut crate::leanh::LeanObject,
    mut v_declName_4165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4166_ = l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(
        v_inst_4163_,
        v_inst_4164_,
        v_declName_4165_,
    );
    return v___x_4166_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0(
    mut v_declName_4167_: *mut crate::leanh::LeanObject,
    mut v_toPure_4168_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4170_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_4169_, v_declName_4167_);
    if crate::leanh::lean_obj_tag(v___x_4170_) == 0 {
        let mut v___x_4171_: u8 = 0;
        let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4171_ = 0;
        v___x_4172_ = crate::leanh::lean_box((v___x_4171_) as usize);
        v___x_4173_ =
            crate::leanh::lean_apply_2(v_toPure_4168_, crate::leanh::lean_box(0), v___x_4172_);
        return v___x_4173_;
    } else {
        let mut v___x_4174_: u8 = 0;
        let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_4170_, 1);
        v___x_4174_ = 1;
        v___x_4175_ = crate::leanh::lean_box((v___x_4174_) as usize);
        v___x_4176_ =
            crate::leanh::lean_apply_2(v_toPure_4168_, crate::leanh::lean_box(0), v___x_4175_);
        return v___x_4176_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isSpecCandidate___redArg(
    mut v_inst_4177_: *mut crate::leanh::LeanObject,
    mut v_inst_4178_: *mut crate::leanh::LeanObject,
    mut v_declName_4179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4180_ = crate::leanh::lean_ctor_get(v_inst_4177_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4180_);
    v_toBind_4181_ = crate::leanh::lean_ctor_get(v_inst_4177_, 1);
    crate::leanh::lean_inc(v_toBind_4181_);
    crate::leanh::lean_dec_ref(v_inst_4177_);
    v_getEnv_4182_ = crate::leanh::lean_ctor_get(v_inst_4178_, 0);
    crate::leanh::lean_inc(v_getEnv_4182_);
    crate::leanh::lean_dec_ref(v_inst_4178_);
    v_toPure_4183_ = crate::leanh::lean_ctor_get(v_toApplicative_4180_, 1);
    crate::leanh::lean_inc(v_toPure_4183_);
    crate::leanh::lean_dec_ref(v_toApplicative_4180_);
    v___f_4184_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4184_, 0, v_declName_4179_);
    crate::leanh::lean_closure_set(v___f_4184_, 1, v_toPure_4183_);
    v___x_4185_ = crate::leanh::lean_apply_4(
        v_toBind_4181_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_4182_,
        v___f_4184_,
    );
    return v___x_4185_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isSpecCandidate(
    mut v_m_4186_: *mut crate::leanh::LeanObject,
    mut v_inst_4187_: *mut crate::leanh::LeanObject,
    mut v_inst_4188_: *mut crate::leanh::LeanObject,
    mut v_declName_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4190_ =
        l_Lean_Compiler_LCNF_isSpecCandidate___redArg(v_inst_4187_, v_inst_4188_, v_declName_4189_);
    return v___x_4190_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: u8 = 0;
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5;
    v___x_4256_ = 0;
    v___x_4257_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_;
    v___x_4258_ = l_Lean_registerTraceClass(v___x_4255_, v___x_4256_, v___x_4257_);
    return v___x_4258_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2____boxed(
    mut v_a_4259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4260_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
    return v_res_4260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_SpecInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_FixedParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instInhabitedSpecState_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedSpecState_default);
    l_Lean_Compiler_LCNF_instInhabitedSpecState =
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedSpecState);
    res = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_specExtension = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_specExtension);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_SpecInfo(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_SpecInfo(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_FixedParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
}
