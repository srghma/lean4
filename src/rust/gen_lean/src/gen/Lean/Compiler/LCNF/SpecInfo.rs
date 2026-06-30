// Lean compiler output
// Module: Lean.Compiler.LCNF.SpecInfo
// Imports: Lean.Compiler.LCNF.FixedParams Lean.Compiler.LCNF.InferType
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_mk, lean_array_push, lean_array_set,
    lean_array_size, lean_array_to_list, lean_array_uget_borrowed, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub, lean_nat_to_int,
    lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_of_nat,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Data::Array::BinSearch::l_Array_binSearchAux___redArg;
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::List::Basic::{l_List_mapTR_loop___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
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
pub static l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__9_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instReprSpecParamInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instReprSpecParamInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__3_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__6_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__12_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__15_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__0_value)
            as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSpecEntry_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0_value:
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
        44, 32, 97, 108, 114, 101, 97, 100, 121, 83, 112, 101, 99, 105, 97, 108, 105, 122, 101,
        100, 63, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_instToMessageDataSpecEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecState_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedSpecState: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_id___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 112, 101, 99, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2852275733072608516 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_SpecState_addEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanClosureObject<4> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 4, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value: leanh::LeanCtorObject<7> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_specExtension: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__1_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__2_value
) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 112, 101, 99, 73, 110, 102, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 99, 111, 109, 112, 117, 116, 101, 83, 112, 101, 99, 69, 110, 116, 114, 105, 101, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_computeSpecEntries___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_computeSpecEntries___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_computeSpecEntries___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5_value:
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
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 102, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2042452093243897853 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__3_value) as *mut leanh::LeanObject,3434285012924019335 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__4_value) as *mut leanh::LeanObject,13745773733782817519 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__6_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_saveSpecEntries___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_saveSpecEntries___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_saveSpecEntries___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1501781890156459336 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4203849195465939425 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 112, 101, 99, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9426862755842527165 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,3947991056360201544 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2285067212717554721 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13153666271249394511 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17406323380265421602 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11322028819074094999 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16051372844745760850 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9403487116094859347 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2146848419678310453 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5968087063485750496 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,463555809555801384 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 513551779 as usize) << 1) | 1) as *mut leanh::LeanObject,4443312571263244686 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4667400838671785689 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12002315305368908305 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,5269381400095652076 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx(
    mut v_x_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2131_) {
        0 => {
            let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2132_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2132_;
        }
        1 => {
            let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2133_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2133_;
        }
        2 => {
            let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2134_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2134_;
        }
        3 => {
            let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2135_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2135_;
        }
        _ => {
            let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2136_ = leanh::lean_unsigned_to_nat(4);
            return v___x_2136_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx___boxed(
    mut v_x_2137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2138_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorIdx(v_x_2137_);
    leanh::lean_dec(v_x_2137_);
    return v_res_2138_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(
    mut v_t_2139_: *mut leanh::LeanObject,
    mut v_k_2140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_2139_) == 0 {
        let mut v_weak_2141_: u8 = 0;
        let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_weak_2141_ = leanh::lean_ctor_get_uint8(v_t_2139_, 0 as u32);
        v___x_2142_ = leanh::lean_box((v_weak_2141_) as usize);
        v___x_2143_ = leanh::lean_apply_1(v_k_2140_, v___x_2142_);
        return v___x_2143_;
    } else {
        return v_k_2140_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg___boxed(
    mut v_t_2144_: *mut leanh::LeanObject,
    mut v_k_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2146_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2144_, v_k_2145_);
    leanh::lean_dec(v_t_2144_);
    return v_res_2146_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim(
    mut v_motive_2147_: *mut leanh::LeanObject,
    mut v_ctorIdx_2148_: *mut leanh::LeanObject,
    mut v_t_2149_: *mut leanh::LeanObject,
    mut v_h_2150_: *mut leanh::LeanObject,
    mut v_k_2151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2152_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2149_, v_k_2151_);
    return v___x_2152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___boxed(
    mut v_motive_2153_: *mut leanh::LeanObject,
    mut v_ctorIdx_2154_: *mut leanh::LeanObject,
    mut v_t_2155_: *mut leanh::LeanObject,
    mut v_h_2156_: *mut leanh::LeanObject,
    mut v_k_2157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim(
        v_motive_2153_,
        v_ctorIdx_2154_,
        v_t_2155_,
        v_h_2156_,
        v_k_2157_,
    );
    leanh::lean_dec(v_t_2155_);
    leanh::lean_dec(v_ctorIdx_2154_);
    return v_res_2158_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg(
    mut v_t_2159_: *mut leanh::LeanObject,
    mut v_fixedInst_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2159_, v_fixedInst_2160_);
    return v___x_2161_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg___boxed(
    mut v_t_2162_: *mut leanh::LeanObject,
    mut v_fixedInst_2163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2164_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___redArg(v_t_2162_, v_fixedInst_2163_);
    leanh::lean_dec(v_t_2162_);
    return v_res_2164_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim(
    mut v_motive_2165_: *mut leanh::LeanObject,
    mut v_t_2166_: *mut leanh::LeanObject,
    mut v_h_2167_: *mut leanh::LeanObject,
    mut v_fixedInst_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2169_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2166_, v_fixedInst_2168_);
    return v___x_2169_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim___boxed(
    mut v_motive_2170_: *mut leanh::LeanObject,
    mut v_t_2171_: *mut leanh::LeanObject,
    mut v_h_2172_: *mut leanh::LeanObject,
    mut v_fixedInst_2173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedInst_elim(
        v_motive_2170_,
        v_t_2171_,
        v_h_2172_,
        v_fixedInst_2173_,
    );
    leanh::lean_dec(v_t_2171_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg(
    mut v_t_2175_: *mut leanh::LeanObject,
    mut v_fixedHO_2176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2175_, v_fixedHO_2176_);
    return v___x_2177_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg___boxed(
    mut v_t_2178_: *mut leanh::LeanObject,
    mut v_fixedHO_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2180_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___redArg(v_t_2178_, v_fixedHO_2179_);
    leanh::lean_dec(v_t_2178_);
    return v_res_2180_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim(
    mut v_motive_2181_: *mut leanh::LeanObject,
    mut v_t_2182_: *mut leanh::LeanObject,
    mut v_h_2183_: *mut leanh::LeanObject,
    mut v_fixedHO_2184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2185_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2182_, v_fixedHO_2184_);
    return v___x_2185_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim___boxed(
    mut v_motive_2186_: *mut leanh::LeanObject,
    mut v_t_2187_: *mut leanh::LeanObject,
    mut v_h_2188_: *mut leanh::LeanObject,
    mut v_fixedHO_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2190_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedHO_elim(
        v_motive_2186_,
        v_t_2187_,
        v_h_2188_,
        v_fixedHO_2189_,
    );
    leanh::lean_dec(v_t_2187_);
    return v_res_2190_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg(
    mut v_t_2191_: *mut leanh::LeanObject,
    mut v_fixedNeutral_2192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2193_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2191_, v_fixedNeutral_2192_);
    return v___x_2193_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg___boxed(
    mut v_t_2194_: *mut leanh::LeanObject,
    mut v_fixedNeutral_2195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2196_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___redArg(
        v_t_2194_,
        v_fixedNeutral_2195_,
    );
    leanh::lean_dec(v_t_2194_);
    return v_res_2196_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim(
    mut v_motive_2197_: *mut leanh::LeanObject,
    mut v_t_2198_: *mut leanh::LeanObject,
    mut v_h_2199_: *mut leanh::LeanObject,
    mut v_fixedNeutral_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2201_ =
        l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2198_, v_fixedNeutral_2200_);
    return v___x_2201_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim___boxed(
    mut v_motive_2202_: *mut leanh::LeanObject,
    mut v_t_2203_: *mut leanh::LeanObject,
    mut v_h_2204_: *mut leanh::LeanObject,
    mut v_fixedNeutral_2205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Lean_Compiler_LCNF_SpecParamInfo_fixedNeutral_elim(
        v_motive_2202_,
        v_t_2203_,
        v_h_2204_,
        v_fixedNeutral_2205_,
    );
    leanh::lean_dec(v_t_2203_);
    return v_res_2206_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg(
    mut v_t_2207_: *mut leanh::LeanObject,
    mut v_user_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2209_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2207_, v_user_2208_);
    return v___x_2209_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg___boxed(
    mut v_t_2210_: *mut leanh::LeanObject,
    mut v_user_2211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2212_ = l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___redArg(v_t_2210_, v_user_2211_);
    leanh::lean_dec(v_t_2210_);
    return v_res_2212_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_user_elim(
    mut v_motive_2213_: *mut leanh::LeanObject,
    mut v_t_2214_: *mut leanh::LeanObject,
    mut v_h_2215_: *mut leanh::LeanObject,
    mut v_user_2216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2214_, v_user_2216_);
    return v___x_2217_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_user_elim___boxed(
    mut v_motive_2218_: *mut leanh::LeanObject,
    mut v_t_2219_: *mut leanh::LeanObject,
    mut v_h_2220_: *mut leanh::LeanObject,
    mut v_user_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2222_ = l_Lean_Compiler_LCNF_SpecParamInfo_user_elim(
        v_motive_2218_,
        v_t_2219_,
        v_h_2220_,
        v_user_2221_,
    );
    leanh::lean_dec(v_t_2219_);
    return v_res_2222_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg(
    mut v_t_2223_: *mut leanh::LeanObject,
    mut v_other_2224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2225_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2223_, v_other_2224_);
    return v___x_2225_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg___boxed(
    mut v_t_2226_: *mut leanh::LeanObject,
    mut v_other_2227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___redArg(v_t_2226_, v_other_2227_);
    leanh::lean_dec(v_t_2226_);
    return v_res_2228_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_other_elim(
    mut v_motive_2229_: *mut leanh::LeanObject,
    mut v_t_2230_: *mut leanh::LeanObject,
    mut v_h_2231_: *mut leanh::LeanObject,
    mut v_other_2232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2233_ = l_Lean_Compiler_LCNF_SpecParamInfo_ctorElim___redArg(v_t_2230_, v_other_2232_);
    return v___x_2233_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_other_elim___boxed(
    mut v_motive_2234_: *mut leanh::LeanObject,
    mut v_t_2235_: *mut leanh::LeanObject,
    mut v_h_2236_: *mut leanh::LeanObject,
    mut v_other_2237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2238_ = l_Lean_Compiler_LCNF_SpecParamInfo_other_elim(
        v_motive_2234_,
        v_t_2235_,
        v_h_2236_,
        v_other_2237_,
    );
    leanh::lean_dec(v_t_2235_);
    return v_res_2238_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2261_ = leanh::lean_unsigned_to_nat(2);
    v___x_2262_ = lean_nat_to_int(v___x_2261_);
    return v___x_2262_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = leanh::lean_unsigned_to_nat(1);
    v___x_2264_ = lean_nat_to_int(v___x_2263_);
    return v___x_2264_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr(
    mut v_x_2265_: *mut leanh::LeanObject,
    mut v_prec_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: u8 = 0;
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: u8 = 0;
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weak_2295_: u8 = 0;
    let mut v___y_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u8 = 0;
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_x_2265_) {
                    0 => {
                        v_weak_2295_ = leanh::lean_ctor_get_uint8(v_x_2265_, 0 as u32);
                        v___x_2305_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_2306_ = lean_nat_dec_le(v___x_2305_, v_prec_2266_);
                        if v___x_2306_ == 0 {
                            v___x_2307_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2297_ = v___x_2307_;
                            state = 5;
                            continue;
                        } else {
                            v___x_2308_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2297_ = v___x_2308_;
                            state = 5;
                            continue;
                        }
                    }
                    1 => {
                        v___x_2309_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_2310_ = lean_nat_dec_le(v___x_2309_, v_prec_2266_);
                        if v___x_2310_ == 0 {
                            v___x_2311_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2268_ = v___x_2311_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2312_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2268_ = v___x_2312_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v___x_2313_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_2314_ = lean_nat_dec_le(v___x_2313_, v_prec_2266_);
                        if v___x_2314_ == 0 {
                            v___x_2315_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2275_ = v___x_2315_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2316_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2275_ = v___x_2316_;
                            state = 2;
                            continue;
                        }
                    }
                    3 => {
                        v___x_2317_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_2318_ = lean_nat_dec_le(v___x_2317_, v_prec_2266_);
                        if v___x_2318_ == 0 {
                            v___x_2319_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2282_ = v___x_2319_;
                            state = 3;
                            continue;
                        } else {
                            v___x_2320_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2282_ = v___x_2320_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2321_ = leanh::lean_unsigned_to_nat(1024);
                        v___x_2322_ = lean_nat_dec_le(v___x_2321_, v_prec_2266_);
                        if v___x_2322_ == 0 {
                            v___x_2323_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__11);
                            v___y_2289_ = v___x_2323_;
                            state = 4;
                            continue;
                        } else {
                            v___x_2324_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12_once), _init_l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__12);
                            v___y_2289_ = v___x_2324_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2269_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__1;
                leanh::lean_inc(v___y_2268_);
                v___x_2270_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2270_, 0, v___y_2268_);
                leanh::lean_ctor_set(v___x_2270_, 1, v___x_2269_);
                v___x_2271_ = 0;
                v___x_2272_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2272_, 0, v___x_2270_);
                leanh::lean_ctor_set_uint8(
                    v___x_2272_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2271_,
                );
                v___x_2273_ = l_Repr_addAppParen(v___x_2272_, v_prec_2266_);
                return v___x_2273_;
            }
            2 => {
                v___x_2276_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__3;
                leanh::lean_inc(v___y_2275_);
                v___x_2277_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2277_, 0, v___y_2275_);
                leanh::lean_ctor_set(v___x_2277_, 1, v___x_2276_);
                v___x_2278_ = 0;
                v___x_2279_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2279_, 0, v___x_2277_);
                leanh::lean_ctor_set_uint8(
                    v___x_2279_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2278_,
                );
                v___x_2280_ = l_Repr_addAppParen(v___x_2279_, v_prec_2266_);
                return v___x_2280_;
            }
            3 => {
                v___x_2283_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__5;
                leanh::lean_inc(v___y_2282_);
                v___x_2284_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2284_, 0, v___y_2282_);
                leanh::lean_ctor_set(v___x_2284_, 1, v___x_2283_);
                v___x_2285_ = 0;
                v___x_2286_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2286_, 0, v___x_2284_);
                leanh::lean_ctor_set_uint8(
                    v___x_2286_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2285_,
                );
                v___x_2287_ = l_Repr_addAppParen(v___x_2286_, v_prec_2266_);
                return v___x_2287_;
            }
            4 => {
                v___x_2290_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__7;
                leanh::lean_inc(v___y_2289_);
                v___x_2291_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2291_, 0, v___y_2289_);
                leanh::lean_ctor_set(v___x_2291_, 1, v___x_2290_);
                v___x_2292_ = 0;
                v___x_2293_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2293_, 0, v___x_2291_);
                leanh::lean_ctor_set_uint8(
                    v___x_2293_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2292_,
                );
                v___x_2294_ = l_Repr_addAppParen(v___x_2293_, v_prec_2266_);
                return v___x_2294_;
            }
            5 => {
                v___x_2298_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr___closed__10;
                v___x_2299_ = l_Bool_repr___redArg(v_weak_2295_);
                v___x_2300_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2300_, 0, v___x_2298_);
                leanh::lean_ctor_set(v___x_2300_, 1, v___x_2299_);
                leanh::lean_inc(v___y_2297_);
                v___x_2301_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2301_, 0, v___y_2297_);
                leanh::lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                v___x_2302_ = 0;
                v___x_2303_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2303_, 0, v___x_2301_);
                leanh::lean_ctor_set_uint8(
                    v___x_2303_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_2325_: *mut leanh::LeanObject,
    mut v_prec_2326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2327_ = l_Lean_Compiler_LCNF_instReprSpecParamInfo_repr(v_x_2325_, v_prec_2326_);
    leanh::lean_dec(v_prec_2326_);
    leanh::lean_dec(v_x_2325_);
    return v_res_2327_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(
    mut v_x_2330_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_2330_) {
        0 => {
            let mut v_weak_2331_: u8 = 0;
            v_weak_2331_ = leanh::lean_ctor_get_uint8(v_x_2330_, 0 as u32);
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
    mut v_x_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2338_: u8 = 0;
    let mut v_r_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lean_Compiler_LCNF_SpecParamInfo_causesSpecialization(v_x_2337_);
    leanh::lean_dec(v_x_2337_);
    v_r_2339_ = leanh::lean_box((v_res_2338_) as usize);
    return v_r_2339_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2343_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__1;
    v___x_2344_ = l_Lean_MessageData_ofFormat(v___x_2343_);
    return v___x_2344_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__4;
    v___x_2349_ = l_Lean_MessageData_ofFormat(v___x_2348_);
    return v___x_2349_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__7;
    v___x_2354_ = l_Lean_MessageData_ofFormat(v___x_2353_);
    return v___x_2354_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__10;
    v___x_2359_ = l_Lean_MessageData_ofFormat(v___x_2358_);
    return v___x_2359_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2363_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__13;
    v___x_2364_ = l_Lean_MessageData_ofFormat(v___x_2363_);
    return v___x_2364_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2368_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__16;
    v___x_2369_ = l_Lean_MessageData_ofFormat(v___x_2368_);
    return v___x_2369_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0(
    mut v_x_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2370_) {
        0 => {
            let mut v_weak_2371_: u8 = 0;
            v_weak_2371_ = leanh::lean_ctor_get_uint8(v_x_2370_, 0 as u32);
            if v_weak_2371_ == 0 {
                let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2372_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
                return v___x_2372_;
            } else {
                let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2373_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
                return v___x_2373_;
            }
        }
        1 => {
            let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2374_ = leanh::lean_obj_once(
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
            let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2375_ = leanh::lean_obj_once(
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
            let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2376_ = leanh::lean_obj_once(
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
            let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2377_ = leanh::lean_obj_once(
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
    mut v_x_2378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2379_ = l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0(v_x_2378_);
    leanh::lean_dec(v_x_2378_);
    return v_res_2379_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2391_ = l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__0;
    v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__2;
    v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
    return v___x_2395_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1(
    mut v___f_2398_: *mut leanh::LeanObject,
    mut v_x_2399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsInfo_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alreadySpecialized_2402_: u8 = 0;
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_2400_ = leanh::lean_ctor_get(v_x_2399_, 0);
                leanh::lean_inc(v_declName_2400_);
                v_paramsInfo_2401_ = leanh::lean_ctor_get(v_x_2399_, 1);
                leanh::lean_inc_ref(v_paramsInfo_2401_);
                v_alreadySpecialized_2402_ = leanh::lean_ctor_get_uint8(
                    v_x_2399_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                leanh::lean_dec_ref(v_x_2399_);
                v___x_2403_ = l_Lean_MessageData_ofName(v_declName_2400_);
                v___x_2404_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__1,
                );
                v___x_2405_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2405_, 0, v___x_2403_);
                leanh::lean_ctor_set(v___x_2405_, 1, v___x_2404_);
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
                leanh::lean_inc_ref(v___y_2407_);
                v___x_2408_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2408_, 0, v___y_2407_);
                v___x_2409_ = l_Lean_MessageData_ofFormat(v___x_2408_);
                v___x_2410_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2410_, 0, v___x_2405_);
                leanh::lean_ctor_set(v___x_2410_, 1, v___x_2409_);
                v___x_2411_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_instToMessageDataSpecEntry___lam__1___closed__3,
                );
                v___x_2412_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2412_, 0, v___x_2410_);
                leanh::lean_ctor_set(v___x_2412_, 1, v___x_2411_);
                v___x_2413_ = lean_array_to_list(v_paramsInfo_2401_);
                v___x_2414_ = leanh::lean_box(0);
                v___x_2415_ = l_List_mapTR_loop___redArg(v___f_2398_, v___x_2413_, v___x_2414_);
                v___x_2416_ = l_Lean_MessageData_ofList(v___x_2415_);
                v___x_2417_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2417_, 0, v___x_2412_);
                leanh::lean_ctor_set(v___x_2417_, 1, v___x_2416_);
                return v___x_2417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2423_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2424_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__0,
    );
    v___x_2425_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
    return v___x_2425_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default()
-> *mut leanh::LeanObject {
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1,
    );
    return v___x_2426_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSpecState() -> *mut leanh::LeanObject {
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
    return v___x_2427_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2428_: *mut leanh::LeanObject,
    mut v_x_2429_: *mut leanh::LeanObject,
    mut v_x_2430_: *mut leanh::LeanObject,
    mut v_x_2431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: u8 = 0;
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2432_ = leanh::lean_ctor_get(v_x_2428_, 0);
                v_vs_2433_ = leanh::lean_ctor_get(v_x_2428_, 1);
                v_isSharedCheck_2457_ = (!leanh::lean_is_exclusive(v_x_2428_)) as u8;
                if v_isSharedCheck_2457_ == 0 {
                    v___x_2435_ = v_x_2428_;
                    v_isShared_2436_ = v_isSharedCheck_2457_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2433_);
                    leanh::lean_inc(v_ks_2432_);
                    leanh::lean_dec(v_x_2428_);
                    v___x_2435_ = leanh::lean_box(0);
                    v_isShared_2436_ = v_isSharedCheck_2457_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2437_ = lean_array_get_size(v_ks_2432_);
                v___x_2438_ = lean_nat_dec_lt(v_x_2429_, v___x_2437_);
                if v___x_2438_ == 0 {
                    leanh::lean_dec(v_x_2429_);
                    v___x_2439_ = lean_array_push(v_ks_2432_, v_x_2430_);
                    v___x_2440_ = lean_array_push(v_vs_2433_, v_x_2431_);
                    if v_isShared_2436_ == 0 {
                        leanh::lean_ctor_set(v___x_2435_, 1, v___x_2440_);
                        leanh::lean_ctor_set(v___x_2435_, 0, v___x_2439_);
                        v___x_2442_ = v___x_2435_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2443_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2439_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2440_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_ks_2432_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_vs_2433_);
                            v___x_2447_ = v_reuseFailAlloc_2451_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2452_ = lean_array_fset(v_ks_2432_, v_x_2429_, v_x_2430_);
                        v___x_2453_ = lean_array_fset(v_vs_2433_, v_x_2429_, v_x_2431_);
                        leanh::lean_dec(v_x_2429_);
                        if v_isShared_2436_ == 0 {
                            leanh::lean_ctor_set(v___x_2435_, 1, v___x_2453_);
                            leanh::lean_ctor_set(v___x_2435_, 0, v___x_2452_);
                            v___x_2455_ = v___x_2435_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2456_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2452_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 1, v___x_2453_);
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
                v___x_2448_ = leanh::lean_unsigned_to_nat(1);
                v___x_2449_ = lean_nat_add(v_x_2429_, v___x_2448_);
                leanh::lean_dec(v_x_2429_);
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
    mut v_n_2458_: *mut leanh::LeanObject,
    mut v_k_2459_: *mut leanh::LeanObject,
    mut v_v_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = leanh::lean_unsigned_to_nat(0);
    v___x_2462_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2458_, v___x_2461_, v_k_2459_, v_v_2460_);
    return v___x_2462_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u64 = 0;
    v___x_2463_ = leanh::lean_unsigned_to_nat(1723);
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
    v___x_2469_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__0);
    v___x_2470_ = lean_usize_sub(v___x_2469_, v___x_2468_);
    return v___x_2470_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2471_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2471_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(
    mut v_x_2472_: *mut leanh::LeanObject,
    mut v_x_2473_: usize,
    mut v_x_2474_: usize,
    mut v_x_2475_: *mut leanh::LeanObject,
    mut v_x_2476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: usize = 0;
    let mut v___x_2480_: usize = 0;
    let mut v___x_2481_: usize = 0;
    let mut v_j_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: u8 = 0;
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v_v_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut v_node_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2512_: u8 = 0;
    let mut v___x_2513_: usize = 0;
    let mut v___x_2514_: usize = 0;
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2519_: u8 = 0;
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut v_unused_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2532_: u8 = 0;
    let mut v_ks_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: usize = 0;
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: u8 = 0;
    let mut v_reuseFailAlloc_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2472_) == 0 {
                    v_es_2477_ = leanh::lean_ctor_get(v_x_2472_, 0);
                    v___x_2478_ = 5usize;
                    v___x_2479_ = 1usize;
                    v___x_2480_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1);
                    v___x_2481_ = lean_usize_land(v_x_2473_, v___x_2480_);
                    v_j_2482_ = lean_usize_to_nat(v___x_2481_);
                    v___x_2483_ = lean_array_get_size(v_es_2477_);
                    v___x_2484_ = lean_nat_dec_lt(v_j_2482_, v___x_2483_);
                    if v___x_2484_ == 0 {
                        leanh::lean_dec(v_j_2482_);
                        leanh::lean_dec(v_x_2476_);
                        leanh::lean_dec(v_x_2475_);
                        return v_x_2472_;
                    } else {
                        leanh::lean_inc_ref(v_es_2477_);
                        v_isSharedCheck_2521_ = (!leanh::lean_is_exclusive(v_x_2472_)) as u8;
                        if v_isSharedCheck_2521_ == 0 {
                            v_unused_2522_ = leanh::lean_ctor_get(v_x_2472_, 0);
                            leanh::lean_dec(v_unused_2522_);
                            v___x_2486_ = v_x_2472_;
                            v_isShared_2487_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2472_);
                            v___x_2486_ = leanh::lean_box(0);
                            v_isShared_2487_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2523_ = leanh::lean_ctor_get(v_x_2472_, 0);
                    v_vs_2524_ = leanh::lean_ctor_get(v_x_2472_, 1);
                    v_isSharedCheck_2544_ = (!leanh::lean_is_exclusive(v_x_2472_)) as u8;
                    if v_isSharedCheck_2544_ == 0 {
                        v___x_2526_ = v_x_2472_;
                        v_isShared_2527_ = v_isSharedCheck_2544_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2524_);
                        leanh::lean_inc(v_ks_2523_);
                        leanh::lean_dec(v_x_2472_);
                        v___x_2526_ = leanh::lean_box(0);
                        v_isShared_2527_ = v_isSharedCheck_2544_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2488_ = lean_array_fget(v_es_2477_, v_j_2482_);
                v___x_2489_ = leanh::lean_box(0);
                v_xs_x27_2490_ = lean_array_fset(v_es_2477_, v_j_2482_, v___x_2489_);
                match leanh::lean_obj_tag(v_v_2488_) {
                    0 => {
                        v_key_2497_ = leanh::lean_ctor_get(v_v_2488_, 0);
                        v_val_2498_ = leanh::lean_ctor_get(v_v_2488_, 1);
                        v_isSharedCheck_2508_ = (!leanh::lean_is_exclusive(v_v_2488_)) as u8;
                        if v_isSharedCheck_2508_ == 0 {
                            v___x_2500_ = v_v_2488_;
                            v_isShared_2501_ = v_isSharedCheck_2508_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2498_);
                            leanh::lean_inc(v_key_2497_);
                            leanh::lean_dec(v_v_2488_);
                            v___x_2500_ = leanh::lean_box(0);
                            v_isShared_2501_ = v_isSharedCheck_2508_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2509_ = leanh::lean_ctor_get(v_v_2488_, 0);
                        v_isSharedCheck_2519_ = (!leanh::lean_is_exclusive(v_v_2488_)) as u8;
                        if v_isSharedCheck_2519_ == 0 {
                            v___x_2511_ = v_v_2488_;
                            v_isShared_2512_ = v_isSharedCheck_2519_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2509_);
                            leanh::lean_dec(v_v_2488_);
                            v___x_2511_ = leanh::lean_box(0);
                            v_isShared_2512_ = v_isSharedCheck_2519_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2520_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2520_, 0, v_x_2475_);
                        leanh::lean_ctor_set(v___x_2520_, 1, v_x_2476_);
                        v___y_2492_ = v___x_2520_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2493_ = lean_array_fset(v_xs_x27_2490_, v_j_2482_, v___y_2492_);
                leanh::lean_dec(v_j_2482_);
                if v_isShared_2487_ == 0 {
                    leanh::lean_ctor_set(v___x_2486_, 0, v___x_2493_);
                    v___x_2495_ = v___x_2486_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
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
                    leanh::lean_del_object(v___x_2500_);
                    v___x_2503_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2497_,
                        v_val_2498_,
                        v_x_2475_,
                        v_x_2476_,
                    );
                    v___x_2504_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2504_, 0, v___x_2503_);
                    v___y_2492_ = v___x_2504_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2498_);
                    leanh::lean_dec(v_key_2497_);
                    if v_isShared_2501_ == 0 {
                        leanh::lean_ctor_set(v___x_2500_, 1, v_x_2476_);
                        leanh::lean_ctor_set(v___x_2500_, 0, v_x_2475_);
                        v___x_2506_ = v___x_2500_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_x_2475_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_x_2476_);
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
                    leanh::lean_ctor_set(v___x_2511_, 0, v___x_2515_);
                    v___x_2517_ = v___x_2511_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2518_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
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
                    v_reuseFailAlloc_2543_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_ks_2523_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_vs_2524_);
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
                    v___x_2541_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2542_ = lean_nat_dec_lt(v___x_2540_, v___x_2541_);
                    leanh::lean_dec(v___x_2540_);
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
                    v_ks_2533_ = leanh::lean_ctor_get(v_newNode_2530_, 0);
                    leanh::lean_inc_ref(v_ks_2533_);
                    v_vs_2534_ = leanh::lean_ctor_get(v_newNode_2530_, 1);
                    leanh::lean_inc_ref(v_vs_2534_);
                    leanh::lean_dec_ref(v_newNode_2530_);
                    v___x_2535_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2536_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__2);
                    v___x_2537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_x_2474_, v_ks_2533_, v_vs_2534_, v___x_2535_, v___x_2536_);
                    leanh::lean_dec_ref(v_vs_2534_);
                    leanh::lean_dec_ref(v_ks_2533_);
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
    mut v_keys_2546_: *mut leanh::LeanObject,
    mut v_vals_2547_: *mut leanh::LeanObject,
    mut v_i_2548_: *mut leanh::LeanObject,
    mut v_entries_2549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v_k_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2555_: u64 = 0;
    let mut v_h_2556_: usize = 0;
    let mut v___x_2557_: usize = 0;
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: usize = 0;
    let mut v___x_2560_: usize = 0;
    let mut v___x_2561_: usize = 0;
    let mut v_h_2562_: usize = 0;
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: u64 = 0;
    let mut v_hash_2567_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2550_ = lean_array_get_size(v_keys_2546_);
                v___x_2551_ = lean_nat_dec_lt(v_i_2548_, v___x_2550_);
                if v___x_2551_ == 0 {
                    leanh::lean_dec(v_i_2548_);
                    return v_entries_2549_;
                } else {
                    v_k_2552_ = lean_array_fget_borrowed(v_keys_2546_, v_i_2548_);
                    v_v_2553_ = lean_array_fget_borrowed(v_vals_2547_, v_i_2548_);
                    if leanh::lean_obj_tag(v_k_2552_) == 0 {
                        v___x_2566_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_2555_ = v___x_2566_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2567_ = leanh::lean_ctor_get_uint64(
                            v_k_2552_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
                v___x_2558_ = leanh::lean_unsigned_to_nat(1);
                v___x_2559_ = 1usize;
                v___x_2560_ = lean_usize_sub(v_depth_2545_, v___x_2559_);
                v___x_2561_ = lean_usize_mul(v___x_2557_, v___x_2560_);
                v_h_2562_ = lean_usize_shift_right(v_h_2556_, v___x_2561_);
                v___x_2563_ = lean_nat_add(v_i_2548_, v___x_2558_);
                leanh::lean_dec(v_i_2548_);
                leanh::lean_inc(v_v_2553_);
                leanh::lean_inc(v_k_2552_);
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
    mut v_depth_2568_: *mut leanh::LeanObject,
    mut v_keys_2569_: *mut leanh::LeanObject,
    mut v_vals_2570_: *mut leanh::LeanObject,
    mut v_i_2571_: *mut leanh::LeanObject,
    mut v_entries_2572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2573_: usize = 0;
    let mut v_res_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2573_ = leanh::lean_unbox_usize(v_depth_2568_);
    leanh::lean_dec(v_depth_2568_);
    v_res_2574_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2573_, v_keys_2569_, v_vals_2570_, v_i_2571_, v_entries_2572_);
    leanh::lean_dec_ref(v_vals_2570_);
    leanh::lean_dec_ref(v_keys_2569_);
    return v_res_2574_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___boxed(
    mut v_x_2575_: *mut leanh::LeanObject,
    mut v_x_2576_: *mut leanh::LeanObject,
    mut v_x_2577_: *mut leanh::LeanObject,
    mut v_x_2578_: *mut leanh::LeanObject,
    mut v_x_2579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_379__boxed_2580_: usize = 0;
    let mut v_x_380__boxed_2581_: usize = 0;
    let mut v_res_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_379__boxed_2580_ = leanh::lean_unbox_usize(v_x_2576_);
    leanh::lean_dec(v_x_2576_);
    v_x_380__boxed_2581_ = leanh::lean_unbox_usize(v_x_2577_);
    leanh::lean_dec(v_x_2577_);
    v_res_2582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_2575_, v_x_379__boxed_2580_, v_x_380__boxed_2581_, v_x_2578_, v_x_2579_);
    return v_res_2582_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(
    mut v_x_2583_: *mut leanh::LeanObject,
    mut v_x_2584_: *mut leanh::LeanObject,
    mut v_x_2585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2587_: u64 = 0;
    let mut v___x_2588_: usize = 0;
    let mut v___x_2589_: usize = 0;
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: u64 = 0;
    let mut v_hash_2592_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2584_) == 0 {
                    v___x_2591_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_2587_ = v___x_2591_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2592_ = leanh::lean_ctor_get_uint64(
                        v_x_2584_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_s_2593_: *mut leanh::LeanObject,
    mut v_e_2594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_declName_2595_ = leanh::lean_ctor_get(v_e_2594_, 0);
    leanh::lean_inc(v_declName_2595_);
    v___x_2596_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_s_2593_, v_declName_2595_, v_e_2594_);
    return v___x_2596_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0(
    mut v_00_u03b2_2597_: *mut leanh::LeanObject,
    mut v_x_2598_: *mut leanh::LeanObject,
    mut v_x_2599_: *mut leanh::LeanObject,
    mut v_x_2600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2601_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0___redArg(v_x_2598_, v_x_2599_, v_x_2600_);
    return v___x_2601_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(
    mut v_00_u03b2_2602_: *mut leanh::LeanObject,
    mut v_x_2603_: *mut leanh::LeanObject,
    mut v_x_2604_: usize,
    mut v_x_2605_: usize,
    mut v_x_2606_: *mut leanh::LeanObject,
    mut v_x_2607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2608_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg(v_x_2603_, v_x_2604_, v_x_2605_, v_x_2606_, v_x_2607_);
    return v___x_2608_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___boxed(
    mut v_00_u03b2_2609_: *mut leanh::LeanObject,
    mut v_x_2610_: *mut leanh::LeanObject,
    mut v_x_2611_: *mut leanh::LeanObject,
    mut v_x_2612_: *mut leanh::LeanObject,
    mut v_x_2613_: *mut leanh::LeanObject,
    mut v_x_2614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_576__boxed_2615_: usize = 0;
    let mut v_x_577__boxed_2616_: usize = 0;
    let mut v_res_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_576__boxed_2615_ = leanh::lean_unbox_usize(v_x_2611_);
    leanh::lean_dec(v_x_2611_);
    v_x_577__boxed_2616_ = leanh::lean_unbox_usize(v_x_2612_);
    leanh::lean_dec(v_x_2612_);
    v_res_2617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0(v_00_u03b2_2609_, v_x_2610_, v_x_576__boxed_2615_, v_x_577__boxed_2616_, v_x_2613_, v_x_2614_);
    return v_res_2617_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2618_: *mut leanh::LeanObject,
    mut v_n_2619_: *mut leanh::LeanObject,
    mut v_k_2620_: *mut leanh::LeanObject,
    mut v_v_2621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2622_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1___redArg(v_n_2619_, v_k_2620_, v_v_2621_);
    return v___x_2622_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2623_: *mut leanh::LeanObject,
    mut v_depth_2624_: usize,
    mut v_keys_2625_: *mut leanh::LeanObject,
    mut v_vals_2626_: *mut leanh::LeanObject,
    mut v_heq_2627_: *mut leanh::LeanObject,
    mut v_i_2628_: *mut leanh::LeanObject,
    mut v_entries_2629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg(v_depth_2624_, v_keys_2625_, v_vals_2626_, v_i_2628_, v_entries_2629_);
    return v___x_2630_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2631_: *mut leanh::LeanObject,
    mut v_depth_2632_: *mut leanh::LeanObject,
    mut v_keys_2633_: *mut leanh::LeanObject,
    mut v_vals_2634_: *mut leanh::LeanObject,
    mut v_heq_2635_: *mut leanh::LeanObject,
    mut v_i_2636_: *mut leanh::LeanObject,
    mut v_entries_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2638_: usize = 0;
    let mut v_res_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2638_ = leanh::lean_unbox_usize(v_depth_2632_);
    leanh::lean_dec(v_depth_2632_);
    v_res_2639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2(v_00_u03b2_2631_, v_depth_boxed_2638_, v_keys_2633_, v_vals_2634_, v_heq_2635_, v_i_2636_, v_entries_2637_);
    leanh::lean_dec_ref(v_vals_2634_);
    leanh::lean_dec_ref(v_keys_2633_);
    return v_res_2639_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2640_: *mut leanh::LeanObject,
    mut v_x_2641_: *mut leanh::LeanObject,
    mut v_x_2642_: *mut leanh::LeanObject,
    mut v_x_2643_: *mut leanh::LeanObject,
    mut v_x_2644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2641_, v_x_2642_, v_x_2643_, v_x_2644_);
    return v___x_2645_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(
    mut v_a_2646_: *mut leanh::LeanObject,
    mut v_b_2647_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_declName_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    v_declName_2648_ = leanh::lean_ctor_get(v_a_2646_, 0);
    v_declName_2649_ = leanh::lean_ctor_get(v_b_2647_, 0);
    v___x_2650_ = l_Lean_Name_quickLt(v_declName_2648_, v_declName_2649_);
    return v___x_2650_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt___boxed(
    mut v_a_2651_: *mut leanh::LeanObject,
    mut v_b_2652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2653_: u8 = 0;
    let mut v_r_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2653_ =
        l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_declLt(v_a_2651_, v_b_2652_);
    leanh::lean_dec_ref(v_b_2652_);
    leanh::lean_dec_ref(v_a_2651_);
    v_r_2654_ = leanh::lean_box((v_res_2653_) as usize);
    return v_r_2654_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries(
    mut v_entries_2656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: u8 = 0;
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: u8 = 0;
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2657_ = lean_array_get_size(v_entries_2656_);
                v___x_2658_ = leanh::lean_unsigned_to_nat(0);
                v___x_2659_ = lean_nat_dec_eq(v___x_2657_, v___x_2658_);
                if v___x_2659_ == 0 {
                    v___x_2660_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_sortEntries___closed__0;
                    v___x_2661_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2662_ = lean_nat_sub(v___x_2657_, v___x_2661_);
                    v___x_2668_ = lean_nat_dec_le(v___x_2658_, v___x_2662_);
                    if v___x_2668_ == 0 {
                        leanh::lean_inc(v___x_2662_);
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
                    leanh::lean_dec(v___x_2662_);
                    leanh::lean_inc(v___y_2664_);
                    v___x_2666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        leanh::lean_box(0),
                        v___x_2660_,
                        v___x_2657_,
                        v_entries_2656_,
                        v___y_2664_,
                        v___y_2664_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    leanh::lean_dec(v___y_2664_);
                    return v___x_2666_;
                } else {
                    v___x_2667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                        leanh::lean_box(0),
                        v___x_2660_,
                        v___x_2657_,
                        v_entries_2656_,
                        v___y_2664_,
                        v___x_2662_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    leanh::lean_dec(v___x_2662_);
                    return v___x_2667_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(
    mut v_entries_2672_: *mut leanh::LeanObject,
    mut v_declName_2673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: u8 = 0;
    v___x_2674_ = leanh::lean_unsigned_to_nat(0);
    v___x_2675_ = lean_array_get_size(v_entries_2672_);
    v___x_2676_ = lean_nat_dec_lt(v___x_2674_, v___x_2675_);
    if v___x_2676_ == 0 {
        let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_declName_2673_);
        v___x_2677_ = leanh::lean_box(0);
        return v___x_2677_;
    } else {
        let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2680_: u8 = 0;
        v___x_2678_ = leanh::lean_unsigned_to_nat(1);
        v___x_2679_ = lean_nat_sub(v___x_2675_, v___x_2678_);
        v___x_2680_ = lean_nat_dec_le(v___x_2674_, v___x_2679_);
        if v___x_2680_ == 0 {
            let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_2679_);
            leanh::lean_dec(v_declName_2673_);
            v___x_2681_ = leanh::lean_box(0);
            return v___x_2681_;
        } else {
            let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2683_: u8 = 0;
            let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2682_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
            v___x_2683_ = 0;
            v___x_2684_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
            leanh::lean_ctor_set(v___x_2684_, 0, v_declName_2673_);
            leanh::lean_ctor_set(v___x_2684_, 1, v___x_2682_);
            leanh::lean_ctor_set_uint8(
                v___x_2684_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_entries_2688_: *mut leanh::LeanObject,
    mut v_declName_2689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f(
        v_entries_2688_,
        v_declName_2689_,
    );
    leanh::lean_dec_ref(v_entries_2688_);
    return v_res_2690_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(
    mut v___y_2691_: *mut leanh::LeanObject,
    mut v___y_2692_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_declName_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: u8 = 0;
    v_declName_2693_ = leanh::lean_ctor_get(v___y_2691_, 0);
    v_declName_2694_ = leanh::lean_ctor_get(v___y_2692_, 0);
    v___x_2695_ = l_Lean_Name_quickLt(v_declName_2693_, v_declName_2694_);
    return v___x_2695_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0___boxed(
    mut v___y_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2698_: u8 = 0;
    let mut v_r_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___y_2696_, v___y_2697_);
    leanh::lean_dec_ref(v___y_2697_);
    leanh::lean_dec_ref(v___y_2696_);
    v_r_2699_ = leanh::lean_box((v_res_2698_) as usize);
    return v_r_2699_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_hi_2700_: *mut leanh::LeanObject,
    mut v_pivot_2701_: *mut leanh::LeanObject,
    mut v_as_2702_: *mut leanh::LeanObject,
    mut v_i_2703_: *mut leanh::LeanObject,
    mut v_k_2704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2705_: u8 = 0;
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: u8 = 0;
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2705_ = lean_nat_dec_lt(v_k_2704_, v_hi_2700_);
                if v___x_2705_ == 0 {
                    leanh::lean_dec(v_k_2704_);
                    v___x_2706_ = lean_array_fswap(v_as_2702_, v_i_2703_, v_hi_2700_);
                    v___x_2707_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2707_, 0, v_i_2703_);
                    leanh::lean_ctor_set(v___x_2707_, 1, v___x_2706_);
                    return v___x_2707_;
                } else {
                    v___x_2708_ = lean_array_fget_borrowed(v_as_2702_, v_k_2704_);
                    v_declName_2709_ = leanh::lean_ctor_get(v___x_2708_, 0);
                    v_declName_2710_ = leanh::lean_ctor_get(v_pivot_2701_, 0);
                    v___x_2711_ = l_Lean_Name_quickLt(v_declName_2709_, v_declName_2710_);
                    if v___x_2711_ == 0 {
                        v___x_2712_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2713_ = lean_nat_add(v_k_2704_, v___x_2712_);
                        leanh::lean_dec(v_k_2704_);
                        v_k_2704_ = v___x_2713_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2715_ = lean_array_fswap(v_as_2702_, v_i_2703_, v_k_2704_);
                        v___x_2716_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2717_ = lean_nat_add(v_i_2703_, v___x_2716_);
                        leanh::lean_dec(v_i_2703_);
                        v___x_2718_ = lean_nat_add(v_k_2704_, v___x_2716_);
                        leanh::lean_dec(v_k_2704_);
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
    mut v_hi_2720_: *mut leanh::LeanObject,
    mut v_pivot_2721_: *mut leanh::LeanObject,
    mut v_as_2722_: *mut leanh::LeanObject,
    mut v_i_2723_: *mut leanh::LeanObject,
    mut v_k_2724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_2720_, v_pivot_2721_, v_as_2722_, v_i_2723_, v_k_2724_);
    leanh::lean_dec_ref(v_pivot_2721_);
    leanh::lean_dec(v_hi_2720_);
    return v_res_2725_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(
    mut v_n_2726_: *mut leanh::LeanObject,
    mut v_as_2727_: *mut leanh::LeanObject,
    mut v_lo_2728_: *mut leanh::LeanObject,
    mut v_hi_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: u8 = 0;
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: u8 = 0;
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: u8 = 0;
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: u8 = 0;
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2741_ = lean_nat_dec_lt(v_lo_2728_, v_hi_2729_);
                if v___x_2741_ == 0 {
                    leanh::lean_dec(v_lo_2728_);
                    return v_as_2727_;
                } else {
                    v___x_2742_ = lean_nat_add(v_lo_2728_, v_hi_2729_);
                    v___x_2743_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2744_ = lean_nat_shiftr(v___x_2742_, v___x_2743_);
                    leanh::lean_dec(v___x_2742_);
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
                leanh::lean_inc_n(v_lo_2728_, 2);
                v___x_2733_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_2729_, v_pivot_2732_, v___y_2731_, v_lo_2728_, v_lo_2728_);
                leanh::lean_dec(v_pivot_2732_);
                v_fst_2734_ = leanh::lean_ctor_get(v___x_2733_, 0);
                leanh::lean_inc(v_fst_2734_);
                v_snd_2735_ = leanh::lean_ctor_get(v___x_2733_, 1);
                leanh::lean_inc(v_snd_2735_);
                leanh::lean_dec_ref(v___x_2733_);
                v___x_2736_ = lean_nat_dec_le(v_hi_2729_, v_fst_2734_);
                if v___x_2736_ == 0 {
                    v___x_2737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_2726_, v_snd_2735_, v_lo_2728_, v_fst_2734_);
                    v___x_2738_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2739_ = lean_nat_add(v_fst_2734_, v___x_2738_);
                    leanh::lean_dec(v_fst_2734_);
                    v_as_2727_ = v___x_2737_;
                    v_lo_2728_ = v___x_2739_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2734_);
                    leanh::lean_dec(v_lo_2728_);
                    return v_snd_2735_;
                }
            }
            2 => {
                v___x_2747_ = lean_array_fget_borrowed(v___y_2746_, v_mid_2744_);
                v___x_2748_ = lean_array_fget_borrowed(v___y_2746_, v_hi_2729_);
                v___x_2749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v___x_2747_, v___x_2748_);
                if v___x_2749_ == 0 {
                    leanh::lean_dec(v_mid_2744_);
                    v___y_2731_ = v___y_2746_;
                    state = 1;
                    continue;
                } else {
                    v___x_2750_ = lean_array_fswap(v___y_2746_, v_mid_2744_, v_hi_2729_);
                    leanh::lean_dec(v_mid_2744_);
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
    mut v_n_2761_: *mut leanh::LeanObject,
    mut v_as_2762_: *mut leanh::LeanObject,
    mut v_lo_2763_: *mut leanh::LeanObject,
    mut v_hi_2764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2765_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_2761_, v_as_2762_, v_lo_2763_, v_hi_2764_);
    leanh::lean_dec(v_hi_2764_);
    leanh::lean_dec(v_n_2761_);
    return v_res_2765_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(
    mut v_s_2766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: u8 = 0;
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: u8 = 0;
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2767_ = lean_array_mk(v_s_2766_);
                v___x_2768_ = lean_array_get_size(v___x_2767_);
                v___x_2769_ = leanh::lean_unsigned_to_nat(0);
                v___x_2770_ = lean_nat_dec_eq(v___x_2768_, v___x_2769_);
                if v___x_2770_ == 0 {
                    v___x_2771_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2772_ = lean_nat_sub(v___x_2768_, v___x_2771_);
                    v___x_2778_ = lean_nat_dec_le(v___x_2769_, v___x_2772_);
                    if v___x_2778_ == 0 {
                        leanh::lean_inc(v___x_2772_);
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
                    leanh::lean_dec(v___x_2772_);
                    leanh::lean_inc(v___y_2774_);
                    v___x_2776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_2768_, v___x_2767_, v___y_2774_, v___y_2774_);
                    leanh::lean_dec(v___y_2774_);
                    return v___x_2776_;
                } else {
                    v___x_2777_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v___x_2768_, v___x_2767_, v___y_2774_, v___x_2772_);
                    leanh::lean_dec(v___x_2772_);
                    return v___x_2777_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(
    mut v_keys_2779_: *mut leanh::LeanObject,
    mut v_i_2780_: *mut leanh::LeanObject,
    mut v_k_2781_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: u8 = 0;
    let mut v_k_x27_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: u8 = 0;
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2782_ = lean_array_get_size(v_keys_2779_);
                v___x_2783_ = lean_nat_dec_lt(v_i_2780_, v___x_2782_);
                if v___x_2783_ == 0 {
                    leanh::lean_dec(v_i_2780_);
                    return v___x_2783_;
                } else {
                    v_k_x27_2784_ = lean_array_fget_borrowed(v_keys_2779_, v_i_2780_);
                    v___x_2785_ = lean_name_eq(v_k_2781_, v_k_x27_2784_);
                    if v___x_2785_ == 0 {
                        v___x_2786_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2787_ = lean_nat_add(v_i_2780_, v___x_2786_);
                        leanh::lean_dec(v_i_2780_);
                        v_i_2780_ = v___x_2787_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_2780_);
                        return v___x_2785_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_2789_: *mut leanh::LeanObject,
    mut v_i_2790_: *mut leanh::LeanObject,
    mut v_k_2791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2792_: u8 = 0;
    let mut v_r_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_2789_, v_i_2790_, v_k_2791_);
    leanh::lean_dec(v_k_2791_);
    leanh::lean_dec_ref(v_keys_2789_);
    v_r_2793_ = leanh::lean_box((v_res_2792_) as usize);
    return v_r_2793_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_x_2794_: *mut leanh::LeanObject,
    mut v_x_2795_: usize,
    mut v_x_2796_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: usize = 0;
    let mut v___x_2800_: usize = 0;
    let mut v___x_2801_: usize = 0;
    let mut v_j_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: u8 = 0;
    let mut v_node_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: usize = 0;
    let mut v___x_2809_: u8 = 0;
    let mut v_ks_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2794_) == 0 {
                    v_es_2797_ = leanh::lean_ctor_get(v_x_2794_, 0);
                    v___x_2798_ = leanh::lean_box(2);
                    v___x_2799_ = 5usize;
                    v___x_2800_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1);
                    v___x_2801_ = lean_usize_land(v_x_2795_, v___x_2800_);
                    v_j_2802_ = lean_usize_to_nat(v___x_2801_);
                    v___x_2803_ = lean_array_get_borrowed(v___x_2798_, v_es_2797_, v_j_2802_);
                    leanh::lean_dec(v_j_2802_);
                    match leanh::lean_obj_tag(v___x_2803_) {
                        0 => {
                            v_key_2804_ = leanh::lean_ctor_get(v___x_2803_, 0);
                            v___x_2805_ = lean_name_eq(v_x_2796_, v_key_2804_);
                            return v___x_2805_;
                        }
                        1 => {
                            v_node_2806_ = leanh::lean_ctor_get(v___x_2803_, 0);
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
                    v_ks_2810_ = leanh::lean_ctor_get(v_x_2794_, 0);
                    v___x_2811_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2812_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_ks_2810_, v___x_2811_, v_x_2796_);
                    return v___x_2812_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(
    mut v_x_2813_: *mut leanh::LeanObject,
    mut v_x_2814_: *mut leanh::LeanObject,
    mut v_x_2815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_476__boxed_2816_: usize = 0;
    let mut v_res_2817_: u8 = 0;
    let mut v_r_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_476__boxed_2816_ = leanh::lean_unbox_usize(v_x_2814_);
    leanh::lean_dec(v_x_2814_);
    v_res_2817_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2813_, v_x_476__boxed_2816_, v_x_2815_);
    leanh::lean_dec(v_x_2815_);
    leanh::lean_dec_ref(v_x_2813_);
    v_r_2818_ = leanh::lean_box((v_res_2817_) as usize);
    return v_r_2818_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_2819_: *mut leanh::LeanObject,
    mut v_x_2820_: *mut leanh::LeanObject,
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
                if leanh::lean_obj_tag(v_x_2820_) == 0 {
                    v___x_2825_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_2822_ = v___x_2825_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2826_ = leanh::lean_ctor_get_uint64(
                        v_x_2820_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_x_2827_: *mut leanh::LeanObject,
    mut v_x_2828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2829_: u8 = 0;
    let mut v_r_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2829_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_2827_, v_x_2828_);
    leanh::lean_dec(v_x_2828_);
    leanh::lean_dec_ref(v_x_2827_);
    v_r_2830_ = leanh::lean_box((v_res_2829_) as usize);
    return v_r_2830_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(
    mut v_x1_2831_: *mut leanh::LeanObject,
    mut v_x2_2832_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_declName_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: u8 = 0;
    v_declName_2833_ = leanh::lean_ctor_get(v_x2_2832_, 0);
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
    mut v_x1_2837_: *mut leanh::LeanObject,
    mut v_x2_2838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2839_: u8 = 0;
    let mut v_r_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2839_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x1_2837_, v_x2_2838_);
    leanh::lean_dec_ref(v_x2_2838_);
    leanh::lean_dec_ref(v_x1_2837_);
    v_r_2840_ = leanh::lean_box((v_res_2839_) as usize);
    return v_r_2840_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(
    mut v_x_2841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2842_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default___closed__1,
    );
    return v___x_2842_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(
    mut v_x_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2844_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_(v_x_2843_);
    leanh::lean_dec_ref(v_x_2843_);
    return v_res_2844_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_;
    v___x_2873_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2872_);
    return v___x_2873_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2____boxed(
    mut v_a_2874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2875_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
    return v_res_2875_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(
    mut v_n_2876_: *mut leanh::LeanObject,
    mut v_as_2877_: *mut leanh::LeanObject,
    mut v_lo_2878_: *mut leanh::LeanObject,
    mut v_hi_2879_: *mut leanh::LeanObject,
    mut v_w_2880_: *mut leanh::LeanObject,
    mut v_hlo_2881_: *mut leanh::LeanObject,
    mut v_hhi_2882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2883_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg(v_n_2876_, v_as_2877_, v_lo_2878_, v_hi_2879_);
    return v___x_2883_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___boxed(
    mut v_n_2884_: *mut leanh::LeanObject,
    mut v_as_2885_: *mut leanh::LeanObject,
    mut v_lo_2886_: *mut leanh::LeanObject,
    mut v_hi_2887_: *mut leanh::LeanObject,
    mut v_w_2888_: *mut leanh::LeanObject,
    mut v_hlo_2889_: *mut leanh::LeanObject,
    mut v_hhi_2890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0(v_n_2884_, v_as_2885_, v_lo_2886_, v_hi_2887_, v_w_2888_, v_hlo_2889_, v_hhi_2890_);
    leanh::lean_dec(v_hi_2887_);
    leanh::lean_dec(v_n_2884_);
    return v_res_2891_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(
    mut v_00_u03b2_2892_: *mut leanh::LeanObject,
    mut v_x_2893_: *mut leanh::LeanObject,
    mut v_x_2894_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2895_: u8 = 0;
    v___x_2895_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___redArg(v_x_2893_, v_x_2894_);
    return v___x_2895_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b2_2896_: *mut leanh::LeanObject,
    mut v_x_2897_: *mut leanh::LeanObject,
    mut v_x_2898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2899_: u8 = 0;
    let mut v_r_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2899_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1(v_00_u03b2_2896_, v_x_2897_, v_x_2898_);
    leanh::lean_dec(v_x_2898_);
    leanh::lean_dec_ref(v_x_2897_);
    v_r_2900_ = leanh::lean_box((v_res_2899_) as usize);
    return v_r_2900_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(
    mut v_n_2901_: *mut leanh::LeanObject,
    mut v_lo_2902_: *mut leanh::LeanObject,
    mut v_hi_2903_: *mut leanh::LeanObject,
    mut v_hhi_2904_: *mut leanh::LeanObject,
    mut v_pivot_2905_: *mut leanh::LeanObject,
    mut v_as_2906_: *mut leanh::LeanObject,
    mut v_i_2907_: *mut leanh::LeanObject,
    mut v_k_2908_: *mut leanh::LeanObject,
    mut v_ilo_2909_: *mut leanh::LeanObject,
    mut v_ik_2910_: *mut leanh::LeanObject,
    mut v_w_2911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2912_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___redArg(v_hi_2903_, v_pivot_2905_, v_as_2906_, v_i_2907_, v_k_2908_);
    return v___x_2912_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_n_2913_: *mut leanh::LeanObject,
    mut v_lo_2914_: *mut leanh::LeanObject,
    mut v_hi_2915_: *mut leanh::LeanObject,
    mut v_hhi_2916_: *mut leanh::LeanObject,
    mut v_pivot_2917_: *mut leanh::LeanObject,
    mut v_as_2918_: *mut leanh::LeanObject,
    mut v_i_2919_: *mut leanh::LeanObject,
    mut v_k_2920_: *mut leanh::LeanObject,
    mut v_ilo_2921_: *mut leanh::LeanObject,
    mut v_ik_2922_: *mut leanh::LeanObject,
    mut v_w_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2924_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0_spec__0(v_n_2913_, v_lo_2914_, v_hi_2915_, v_hhi_2916_, v_pivot_2917_, v_as_2918_, v_i_2919_, v_k_2920_, v_ilo_2921_, v_ik_2922_, v_w_2923_);
    leanh::lean_dec_ref(v_pivot_2917_);
    leanh::lean_dec(v_hi_2915_);
    leanh::lean_dec(v_lo_2914_);
    leanh::lean_dec(v_n_2913_);
    return v_res_2924_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(
    mut v_00_u03b2_2925_: *mut leanh::LeanObject,
    mut v_x_2926_: *mut leanh::LeanObject,
    mut v_x_2927_: usize,
    mut v_x_2928_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2929_: u8 = 0;
    v___x_2929_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_2926_, v_x_2927_, v_x_2928_);
    return v___x_2929_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_00_u03b2_2930_: *mut leanh::LeanObject,
    mut v_x_2931_: *mut leanh::LeanObject,
    mut v_x_2932_: *mut leanh::LeanObject,
    mut v_x_2933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_656__boxed_2934_: usize = 0;
    let mut v_res_2935_: u8 = 0;
    let mut v_r_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_656__boxed_2934_ = leanh::lean_unbox_usize(v_x_2932_);
    leanh::lean_dec(v_x_2932_);
    v_res_2935_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_2930_, v_x_2931_, v_x_656__boxed_2934_, v_x_2933_);
    leanh::lean_dec(v_x_2933_);
    leanh::lean_dec_ref(v_x_2931_);
    v_r_2936_ = leanh::lean_box((v_res_2935_) as usize);
    return v_r_2936_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(
    mut v_00_u03b2_2937_: *mut leanh::LeanObject,
    mut v_keys_2938_: *mut leanh::LeanObject,
    mut v_vals_2939_: *mut leanh::LeanObject,
    mut v_heq_2940_: *mut leanh::LeanObject,
    mut v_i_2941_: *mut leanh::LeanObject,
    mut v_k_2942_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2943_: u8 = 0;
    v___x_2943_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_keys_2938_, v_i_2941_, v_k_2942_);
    return v___x_2943_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_2944_: *mut leanh::LeanObject,
    mut v_keys_2945_: *mut leanh::LeanObject,
    mut v_vals_2946_: *mut leanh::LeanObject,
    mut v_heq_2947_: *mut leanh::LeanObject,
    mut v_i_2948_: *mut leanh::LeanObject,
    mut v_k_2949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2950_: u8 = 0;
    let mut v_r_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03b2_2944_, v_keys_2945_, v_vals_2946_, v_heq_2947_, v_i_2948_, v_k_2949_);
    leanh::lean_dec(v_k_2949_);
    leanh::lean_dec_ref(v_vals_2946_);
    leanh::lean_dec_ref(v_keys_2945_);
    v_r_2951_ = leanh::lean_box((v_res_2950_) as usize);
    return v_r_2951_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(
    mut v_env_2952_: *mut leanh::LeanObject,
    mut v_type_2953_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_body_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_type_2953_) == 7 {
                    v_body_2954_ = leanh::lean_ctor_get(v_type_2953_, 2);
                    v_type_2953_ = v_body_2954_;
                    state = 0;
                    continue;
                } else {
                    v___x_2956_ = l_Lean_Expr_getAppFn(v_type_2953_);
                    if leanh::lean_obj_tag(v___x_2956_) == 4 {
                        v_declName_2957_ = leanh::lean_ctor_get(v___x_2956_, 0);
                        leanh::lean_inc(v_declName_2957_);
                        leanh::lean_dec_ref_known(v___x_2956_, 2);
                        v___x_2958_ =
                            l_Lean_Compiler_hasNospecializeAttribute(v_env_2952_, v_declName_2957_);
                        return v___x_2958_;
                    } else {
                        leanh::lean_dec_ref(v___x_2956_);
                        leanh::lean_dec_ref(v_env_2952_);
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
    mut v_env_2960_: *mut leanh::LeanObject,
    mut v_type_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2962_: u8 = 0;
    let mut v_r_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2962_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isNoSpecType(
        v_env_2960_,
        v_type_2961_,
    );
    leanh::lean_dec_ref(v_type_2961_);
    v_r_2963_ = leanh::lean_box((v_res_2962_) as usize);
    return v_r_2963_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(
    mut v_env_2964_: *mut leanh::LeanObject,
    mut v_type_2965_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_body_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: u8 = 0;
    let mut v___x_2971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_type_2965_) == 7 {
                    v_body_2966_ = leanh::lean_ctor_get(v_type_2965_, 2);
                    v_type_2965_ = v_body_2966_;
                    state = 0;
                    continue;
                } else {
                    v___x_2968_ = l_Lean_Expr_getAppFn(v_type_2965_);
                    if leanh::lean_obj_tag(v___x_2968_) == 4 {
                        v_declName_2969_ = leanh::lean_ctor_get(v___x_2968_, 0);
                        leanh::lean_inc(v_declName_2969_);
                        leanh::lean_dec_ref_known(v___x_2968_, 2);
                        v___x_2970_ = l_Lean_Compiler_hasWeakSpecializeAttribute(
                            v_env_2964_,
                            v_declName_2969_,
                        );
                        return v___x_2970_;
                    } else {
                        leanh::lean_dec_ref(v___x_2968_);
                        leanh::lean_dec_ref(v_env_2964_);
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
    mut v_env_2972_: *mut leanh::LeanObject,
    mut v_type_2973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2974_: u8 = 0;
    let mut v_r_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2974_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(
        v_env_2972_,
        v_type_2973_,
    );
    leanh::lean_dec_ref(v_type_2973_);
    v_r_2975_ = leanh::lean_box((v_res_2974_) as usize);
    return v_r_2975_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(
    mut v___x_2979_: *mut leanh::LeanObject,
    mut v_param_2980_: *mut leanh::LeanObject,
    mut v_paramsInfo_2981_: *mut leanh::LeanObject,
    mut v_upperBound_2982_: *mut leanh::LeanObject,
    mut v_a_2983_: *mut leanh::LeanObject,
    mut v_b_2984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weak_3005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2990_ = lean_nat_dec_lt(v_a_2983_, v_upperBound_2982_);
                if v___x_2990_ == 0 {
                    leanh::lean_dec(v_a_2983_);
                    leanh::lean_inc_ref(v_b_2984_);
                    return v_b_2984_;
                } else {
                    v___x_2991_ = leanh::lean_box(0);
                    v___x_2992_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0;
                    v___x_3001_ = l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default;
                    v___x_3004_ =
                        lean_array_get_borrowed(v___x_3001_, v_paramsInfo_2981_, v_a_2983_);
                    match leanh::lean_obj_tag(v___x_3004_) {
                        0 => {
                            v_weak_3005_ = leanh::lean_ctor_get_uint8(v___x_3004_, 0 as u32);
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
                v___x_2987_ = leanh::lean_unsigned_to_nat(1);
                v___x_2988_ = lean_nat_add(v_a_2983_, v___x_2987_);
                leanh::lean_dec(v_a_2983_);
                v_a_2983_ = v___x_2988_;
                v_b_2984_ = v_a_2986_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2994_ = lean_array_fget_borrowed(v___x_2979_, v_a_2983_);
                v_type_2995_ = leanh::lean_ctor_get(v___x_2994_, 2);
                v_fvarId_2996_ = leanh::lean_ctor_get(v_param_2980_, 0);
                v___x_2997_ = l_Lean_Expr_containsFVar(v_type_2995_, v_fvarId_2996_);
                if v___x_2997_ == 0 {
                    v_a_2986_ = v___x_2992_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_2983_);
                    v___x_2998_ = leanh::lean_box((v___x_2997_) as usize);
                    v___x_2999_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2999_, 0, v___x_2998_);
                    v___x_3000_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3000_, 0, v___x_2999_);
                    leanh::lean_ctor_set(v___x_3000_, 1, v___x_2991_);
                    return v___x_3000_;
                }
            }
            3 => {
                v___x_3003_ = lean_array_get_borrowed(v___x_3001_, v_paramsInfo_2981_, v_a_2983_);
                if leanh::lean_obj_tag(v___x_3003_) == 0 {
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
    mut v___x_3006_: *mut leanh::LeanObject,
    mut v_param_3007_: *mut leanh::LeanObject,
    mut v_paramsInfo_3008_: *mut leanh::LeanObject,
    mut v_upperBound_3009_: *mut leanh::LeanObject,
    mut v_a_3010_: *mut leanh::LeanObject,
    mut v_b_3011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3012_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_3006_, v_param_3007_, v_paramsInfo_3008_, v_upperBound_3009_, v_a_3010_, v_b_3011_);
    leanh::lean_dec_ref(v_b_3011_);
    leanh::lean_dec(v_upperBound_3009_);
    leanh::lean_dec_ref(v_paramsInfo_3008_);
    leanh::lean_dec_ref(v_param_3007_);
    leanh::lean_dec_ref(v___x_3006_);
    return v_res_3012_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3013_ = 0;
    v___x_3014_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_3013_);
    return v___x_3014_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(
    mut v_decl_3015_: *mut leanh::LeanObject,
    mut v_paramsInfo_3016_: *mut leanh::LeanObject,
    mut v_j_3017_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toSignature_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_param_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toSignature_3018_ = leanh::lean_ctor_get(v_decl_3015_, 0);
    v_params_3019_ = leanh::lean_ctor_get(v_toSignature_3018_, 3);
    v___x_3020_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___closed__0);
    v___x_3021_ = leanh::lean_unsigned_to_nat(1);
    v___x_3022_ = lean_nat_add(v_j_3017_, v___x_3021_);
    v___x_3023_ = lean_array_get_size(v_params_3019_);
    v___x_3024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg___closed__0;
    v_param_3025_ = lean_array_get_borrowed(v___x_3020_, v_params_3019_, v_j_3017_);
    v___x_3026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v_params_3019_, v_param_3025_, v_paramsInfo_3016_, v___x_3023_, v___x_3022_, v___x_3024_);
    v_fst_3027_ = leanh::lean_ctor_get(v___x_3026_, 0);
    leanh::lean_inc(v_fst_3027_);
    leanh::lean_dec_ref(v___x_3026_);
    if leanh::lean_obj_tag(v_fst_3027_) == 0 {
        let mut v___x_3028_: u8 = 0;
        v___x_3028_ = 0;
        return v___x_3028_;
    } else {
        let mut v_val_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3030_: u8 = 0;
        v_val_3029_ = leanh::lean_ctor_get(v_fst_3027_, 0);
        leanh::lean_inc(v_val_3029_);
        leanh::lean_dec_ref_known(v_fst_3027_, 1);
        v___x_3030_ = (leanh::lean_unbox(v_val_3029_) as u8);
        leanh::lean_dec(v_val_3029_);
        return v___x_3030_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps___boxed(
    mut v_decl_3031_: *mut leanh::LeanObject,
    mut v_paramsInfo_3032_: *mut leanh::LeanObject,
    mut v_j_3033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3034_: u8 = 0;
    let mut v_r_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3034_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(
        v_decl_3031_,
        v_paramsInfo_3032_,
        v_j_3033_,
    );
    leanh::lean_dec(v_j_3033_);
    leanh::lean_dec_ref(v_paramsInfo_3032_);
    leanh::lean_dec_ref(v_decl_3031_);
    v_r_3035_ = leanh::lean_box((v_res_3034_) as usize);
    return v_r_3035_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(
    mut v___x_3036_: *mut leanh::LeanObject,
    mut v_param_3037_: *mut leanh::LeanObject,
    mut v_paramsInfo_3038_: *mut leanh::LeanObject,
    mut v_upperBound_3039_: *mut leanh::LeanObject,
    mut v_inst_3040_: *mut leanh::LeanObject,
    mut v_R_3041_: *mut leanh::LeanObject,
    mut v_a_3042_: *mut leanh::LeanObject,
    mut v_b_3043_: *mut leanh::LeanObject,
    mut v_c_3044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___redArg(v___x_3036_, v_param_3037_, v_paramsInfo_3038_, v_upperBound_3039_, v_a_3042_, v_b_3043_);
    return v___x_3045_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0___boxed(
    mut v___x_3046_: *mut leanh::LeanObject,
    mut v_param_3047_: *mut leanh::LeanObject,
    mut v_paramsInfo_3048_: *mut leanh::LeanObject,
    mut v_upperBound_3049_: *mut leanh::LeanObject,
    mut v_inst_3050_: *mut leanh::LeanObject,
    mut v_R_3051_: *mut leanh::LeanObject,
    mut v_a_3052_: *mut leanh::LeanObject,
    mut v_b_3053_: *mut leanh::LeanObject,
    mut v_c_3054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps_spec__0(v___x_3046_, v_param_3047_, v_paramsInfo_3048_, v_upperBound_3049_, v_inst_3050_, v_R_3051_, v_a_3052_, v_b_3053_, v_c_3054_);
    leanh::lean_dec_ref(v_b_3053_);
    leanh::lean_dec(v_upperBound_3049_);
    leanh::lean_dec_ref(v_paramsInfo_3048_);
    leanh::lean_dec_ref(v_param_3047_);
    leanh::lean_dec_ref(v___x_3046_);
    return v_res_3055_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3056_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_3056_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(
    mut v_msg_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
    mut v___y_3061_: *mut leanh::LeanObject,
    mut v___y_3062_: *mut leanh::LeanObject,
    mut v___y_3063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3070_: u8 = 0;
    let mut v_toFunctor_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3077_: u8 = 0;
    let mut v___f_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11117__overap_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3098_: u8 = 0;
    let mut v_unused_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3100_: u8 = 0;
    let mut v_unused_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3065_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___closed__0);
                v___x_3066_ = l_StateRefT_x27_instMonad___redArg(v___x_3065_);
                v_toApplicative_3067_ = leanh::lean_ctor_get(v___x_3066_, 0);
                v_isSharedCheck_3100_ = (!leanh::lean_is_exclusive(v___x_3066_)) as u8;
                if v_isSharedCheck_3100_ == 0 {
                    v_unused_3101_ = leanh::lean_ctor_get(v___x_3066_, 1);
                    leanh::lean_dec(v_unused_3101_);
                    v___x_3069_ = v___x_3066_;
                    v_isShared_3070_ = v_isSharedCheck_3100_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3067_);
                    leanh::lean_dec(v___x_3066_);
                    v___x_3069_ = leanh::lean_box(0);
                    v_isShared_3070_ = v_isSharedCheck_3100_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3071_ = leanh::lean_ctor_get(v_toApplicative_3067_, 0);
                v_toSeq_3072_ = leanh::lean_ctor_get(v_toApplicative_3067_, 2);
                v_toSeqLeft_3073_ = leanh::lean_ctor_get(v_toApplicative_3067_, 3);
                v_toSeqRight_3074_ = leanh::lean_ctor_get(v_toApplicative_3067_, 4);
                v_isSharedCheck_3098_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3067_)) as u8;
                if v_isSharedCheck_3098_ == 0 {
                    v_unused_3099_ = leanh::lean_ctor_get(v_toApplicative_3067_, 1);
                    leanh::lean_dec(v_unused_3099_);
                    v___x_3076_ = v_toApplicative_3067_;
                    v_isShared_3077_ = v_isSharedCheck_3098_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3074_);
                    leanh::lean_inc(v_toSeqLeft_3073_);
                    leanh::lean_inc(v_toSeq_3072_);
                    leanh::lean_inc(v_toFunctor_3071_);
                    leanh::lean_dec(v_toApplicative_3067_);
                    v___x_3076_ = leanh::lean_box(0);
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
                leanh::lean_inc_ref(v_toFunctor_3071_);
                v___f_3080_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3080_, 0, v_toFunctor_3071_);
                v___f_3081_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3081_, 0, v_toFunctor_3071_);
                v___x_3082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3082_, 0, v___f_3080_);
                leanh::lean_ctor_set(v___x_3082_, 1, v___f_3081_);
                v___f_3083_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3083_, 0, v_toSeqRight_3074_);
                v___f_3084_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3084_, 0, v_toSeqLeft_3073_);
                v___f_3085_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3085_, 0, v_toSeq_3072_);
                if v_isShared_3077_ == 0 {
                    leanh::lean_ctor_set(v___x_3076_, 4, v___f_3083_);
                    leanh::lean_ctor_set(v___x_3076_, 3, v___f_3084_);
                    leanh::lean_ctor_set(v___x_3076_, 2, v___f_3085_);
                    leanh::lean_ctor_set(v___x_3076_, 1, v___f_3078_);
                    leanh::lean_ctor_set(v___x_3076_, 0, v___x_3082_);
                    v___x_3087_ = v___x_3076_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3097_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___f_3078_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 2, v___f_3085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 3, v___f_3084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 4, v___f_3083_);
                    v___x_3087_ = v_reuseFailAlloc_3097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3070_ == 0 {
                    leanh::lean_ctor_set(v___x_3069_, 1, v___f_3079_);
                    leanh::lean_ctor_set(v___x_3069_, 0, v___x_3087_);
                    v___x_3089_ = v___x_3069_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 1, v___f_3079_);
                    v___x_3089_ = v_reuseFailAlloc_3096_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3090_ = l_StateRefT_x27_instMonad___redArg(v___x_3089_);
                v___x_3091_ = leanh::lean_box(0);
                v___x_3092_ = l_instInhabitedOfMonad___redArg(v___x_3090_, v___x_3091_);
                v___f_3093_ = leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3093_, 0, v___x_3092_);
                v___x_11117__overap_3094_ = lean_panic_fn_borrowed(v___f_3093_, v_msg_3059_);
                leanh::lean_dec_ref(v___f_3093_);
                leanh::lean_inc(v___y_3063_);
                leanh::lean_inc_ref(v___y_3062_);
                leanh::lean_inc(v___y_3061_);
                leanh::lean_inc_ref(v___y_3060_);
                v___x_3095_ = leanh::lean_apply_5(
                    v___x_11117__overap_3094_,
                    v___y_3060_,
                    v___y_3061_,
                    v___y_3062_,
                    v___y_3063_,
                    leanh::lean_box(0),
                );
                return v___x_3095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8___boxed(
    mut v_msg_3102_: *mut leanh::LeanObject,
    mut v___y_3103_: *mut leanh::LeanObject,
    mut v___y_3104_: *mut leanh::LeanObject,
    mut v___y_3105_: *mut leanh::LeanObject,
    mut v___y_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3108_ = l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(
        v_msg_3102_,
        v___y_3103_,
        v___y_3104_,
        v___y_3105_,
        v___y_3106_,
    );
    leanh::lean_dec(v___y_3106_);
    leanh::lean_dec_ref(v___y_3105_);
    leanh::lean_dec(v___y_3104_);
    leanh::lean_dec_ref(v___y_3103_);
    return v_res_3108_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(
    mut v_a_3109_: *mut leanh::LeanObject,
    mut v_as_3110_: *mut leanh::LeanObject,
    mut v_i_3111_: usize,
    mut v_stop_3112_: usize,
) -> u8 {
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_3120_: *mut leanh::LeanObject,
    mut v_as_3121_: *mut leanh::LeanObject,
    mut v_i_3122_: *mut leanh::LeanObject,
    mut v_stop_3123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3124_: usize = 0;
    let mut v_stop_boxed_3125_: usize = 0;
    let mut v_res_3126_: u8 = 0;
    let mut v_r_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3124_ = leanh::lean_unbox_usize(v_i_3122_);
    leanh::lean_dec(v_i_3122_);
    v_stop_boxed_3125_ = leanh::lean_unbox_usize(v_stop_3123_);
    leanh::lean_dec(v_stop_3123_);
    v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0_spec__0(v_a_3120_, v_as_3121_, v_i_boxed_3124_, v_stop_boxed_3125_);
    leanh::lean_dec_ref(v_as_3121_);
    leanh::lean_dec(v_a_3120_);
    v_r_3127_ = leanh::lean_box((v_res_3126_) as usize);
    return v_r_3127_;
}
pub unsafe fn l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(
    mut v_as_3128_: *mut leanh::LeanObject,
    mut v_a_3129_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: u8 = 0;
    v___x_3130_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_as_3136_: *mut leanh::LeanObject,
    mut v_a_3137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3138_: u8 = 0;
    let mut v_r_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3138_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(
        v_as_3136_, v_a_3137_,
    );
    leanh::lean_dec(v_a_3137_);
    leanh::lean_dec_ref(v_as_3136_);
    v_r_3139_ = leanh::lean_box((v_res_3138_) as usize);
    return v_r_3139_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(
    mut v_b_3140_: *mut leanh::LeanObject,
    mut v_info_3141_: *mut leanh::LeanObject,
    mut v___y_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
    mut v___y_3144_: *mut leanh::LeanObject,
    mut v___y_3145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3147_ = lean_array_push(v_b_3140_, v_info_3141_);
    v___x_3148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3148_, 0, v___x_3147_);
    v___x_3149_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3149_, 0, v___x_3148_);
    return v___x_3149_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0___boxed(
    mut v_b_3150_: *mut leanh::LeanObject,
    mut v_info_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
    mut v___y_3153_: *mut leanh::LeanObject,
    mut v___y_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3157_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3150_, v_info_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
    leanh::lean_dec(v___y_3155_);
    leanh::lean_dec_ref(v___y_3154_);
    leanh::lean_dec(v___y_3153_);
    leanh::lean_dec_ref(v___y_3152_);
    return v_res_3157_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(
    mut v_upperBound_3160_: *mut leanh::LeanObject,
    mut v___x_3161_: *mut leanh::LeanObject,
    mut v_autoSpecialize_3162_: *mut leanh::LeanObject,
    mut v___x_3163_: *mut leanh::LeanObject,
    mut v___x_3164_: *mut leanh::LeanObject,
    mut v_a_3165_: *mut leanh::LeanObject,
    mut v_b_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
    mut v___y_3168_: *mut leanh::LeanObject,
    mut v___y_3169_: *mut leanh::LeanObject,
    mut v___y_3170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v_a_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_a_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v___x_3195_: u8 = 0;
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: u8 = 0;
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v_val_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: u8 = 0;
    let mut v_a_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3195_ = lean_nat_dec_lt(v_a_3165_, v_upperBound_3160_);
                if v___x_3195_ == 0 {
                    leanh::lean_dec(v_a_3165_);
                    leanh::lean_dec(v___x_3164_);
                    leanh::lean_dec(v___x_3163_);
                    leanh::lean_dec_ref(v_autoSpecialize_3162_);
                    v___x_3196_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3196_, 0, v_b_3166_);
                    return v___x_3196_;
                } else {
                    v___x_3197_ = lean_st_ref_get(v___y_3170_);
                    v___x_3198_ = lean_array_fget_borrowed(v___x_3161_, v_a_3165_);
                    v_type_3199_ = leanh::lean_ctor_get(v___x_3198_, 2);
                    leanh::lean_inc_ref(v_type_3199_);
                    v___x_3200_ =
                        l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_3199_, v___y_3170_);
                    if leanh::lean_obj_tag(v___x_3200_) == 0 {
                        v_a_3201_ = leanh::lean_ctor_get(v___x_3200_, 0);
                        leanh::lean_inc(v_a_3201_);
                        leanh::lean_dec_ref_known(v___x_3200_, 1);
                        v_env_3202_ = leanh::lean_ctor_get(v___x_3197_, 0);
                        leanh::lean_inc_ref(v_env_3202_);
                        leanh::lean_dec(v___x_3197_);
                        if leanh::lean_obj_tag(v___x_3164_) == 0 {
                            v___x_3226_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___closed__0;
                            v___x_3227_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v___x_3226_, v_a_3165_);
                            v___y_3213_ = v___x_3227_;
                            state = 8;
                            continue;
                        } else {
                            v_val_3228_ = leanh::lean_ctor_get(v___x_3164_, 0);
                            v___x_3229_ = l_Array_contains___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__0(v_val_3228_, v_a_3165_);
                            v___y_3213_ = v___x_3229_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3197_);
                        leanh::lean_dec_ref(v_b_3166_);
                        leanh::lean_dec(v_a_3165_);
                        leanh::lean_dec(v___x_3164_);
                        leanh::lean_dec(v___x_3163_);
                        leanh::lean_dec_ref(v_autoSpecialize_3162_);
                        v_a_3230_ = leanh::lean_ctor_get(v___x_3200_, 0);
                        v_isSharedCheck_3237_ =
                            (!leanh::lean_is_exclusive(v___x_3200_)) as u8;
                        if v_isSharedCheck_3237_ == 0 {
                            v___x_3232_ = v___x_3200_;
                            v_isShared_3233_ = v_isSharedCheck_3237_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3230_);
                            leanh::lean_dec(v___x_3200_);
                            v___x_3232_ = leanh::lean_box(0);
                            v_isShared_3233_ = v_isSharedCheck_3237_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_3173_) == 0 {
                    v_a_3174_ = leanh::lean_ctor_get(v___y_3173_, 0);
                    v_isSharedCheck_3186_ = (!leanh::lean_is_exclusive(v___y_3173_)) as u8;
                    if v_isSharedCheck_3186_ == 0 {
                        v___x_3176_ = v___y_3173_;
                        v_isShared_3177_ = v_isSharedCheck_3186_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3174_);
                        leanh::lean_dec(v___y_3173_);
                        v___x_3176_ = leanh::lean_box(0);
                        v_isShared_3177_ = v_isSharedCheck_3186_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3165_);
                    leanh::lean_dec(v___x_3164_);
                    leanh::lean_dec(v___x_3163_);
                    leanh::lean_dec_ref(v_autoSpecialize_3162_);
                    v_a_3187_ = leanh::lean_ctor_get(v___y_3173_, 0);
                    v_isSharedCheck_3194_ = (!leanh::lean_is_exclusive(v___y_3173_)) as u8;
                    if v_isSharedCheck_3194_ == 0 {
                        v___x_3189_ = v___y_3173_;
                        v_isShared_3190_ = v_isSharedCheck_3194_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3187_);
                        leanh::lean_dec(v___y_3173_);
                        v___x_3189_ = leanh::lean_box(0);
                        v_isShared_3190_ = v_isSharedCheck_3194_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3174_) == 0 {
                    leanh::lean_dec(v_a_3165_);
                    leanh::lean_dec(v___x_3164_);
                    leanh::lean_dec(v___x_3163_);
                    leanh::lean_dec_ref(v_autoSpecialize_3162_);
                    v_a_3178_ = leanh::lean_ctor_get(v_a_3174_, 0);
                    leanh::lean_inc(v_a_3178_);
                    leanh::lean_dec_ref_known(v_a_3174_, 1);
                    if v_isShared_3177_ == 0 {
                        leanh::lean_ctor_set(v___x_3176_, 0, v_a_3178_);
                        v___x_3180_ = v___x_3176_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3181_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3178_);
                        v___x_3180_ = v_reuseFailAlloc_3181_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3176_);
                    v_a_3182_ = leanh::lean_ctor_get(v_a_3174_, 0);
                    leanh::lean_inc(v_a_3182_);
                    leanh::lean_dec_ref_known(v_a_3174_, 1);
                    v___x_3183_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3184_ = lean_nat_add(v_a_3165_, v___x_3183_);
                    leanh::lean_dec(v_a_3165_);
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
                    v_reuseFailAlloc_3193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
                    v___x_3192_ = v_reuseFailAlloc_3193_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3192_;
            }
            6 => {
                v___x_3204_ = leanh::lean_box(4);
                v___x_3205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3166_, v___x_3204_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                v___y_3173_ = v___x_3205_;
                state = 1;
                continue;
            }
            7 => {
                v___x_3207_ = lean_st_ref_get(v___y_3170_);
                v_env_3208_ = leanh::lean_ctor_get(v___x_3207_, 0);
                leanh::lean_inc_ref(v_env_3208_);
                leanh::lean_dec(v___x_3207_);
                v___x_3209_ =
                    l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_isWeakSpecType(
                        v_env_3208_,
                        v_type_3199_,
                    );
                v___x_3210_ = leanh::lean_alloc_ctor(0, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_3210_, 0 as u32, v___x_3209_);
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
                        leanh::lean_inc_ref(v_type_3199_);
                        v___x_3215_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_3199_);
                        if v___x_3215_ == 0 {
                            if leanh::lean_obj_tag(v_a_3201_) == 0 {
                                if v___x_3215_ == 0 {
                                    leanh::lean_inc_ref(v_autoSpecialize_3162_);
                                    leanh::lean_inc(v___x_3164_);
                                    leanh::lean_inc(v___x_3163_);
                                    v___x_3216_ = leanh::lean_apply_2(
                                        v_autoSpecialize_3162_,
                                        v___x_3163_,
                                        v___x_3164_,
                                    );
                                    v___x_3217_ = (leanh::lean_unbox(v___x_3216_) as u8);
                                    if v___x_3217_ == 0 {
                                        state = 6;
                                        continue;
                                    } else {
                                        if leanh::lean_obj_tag(v_type_3199_) == 7 {
                                            v___x_3218_ = leanh::lean_box(1);
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
                                leanh::lean_dec_ref_known(v_a_3201_, 1);
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3201_);
                            v___x_3220_ = leanh::lean_box(2);
                            v___x_3221_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3166_, v___x_3220_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                            v___y_3173_ = v___x_3221_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3201_);
                        v___x_3222_ = leanh::lean_box(4);
                        v___x_3223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg___lam__0(v_b_3166_, v___x_3222_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
                        v___y_3173_ = v___x_3223_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3202_);
                    leanh::lean_dec(v_a_3201_);
                    v___x_3224_ = leanh::lean_box(3);
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
                    v_reuseFailAlloc_3236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
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
    mut v_upperBound_3238_: *mut leanh::LeanObject,
    mut v___x_3239_: *mut leanh::LeanObject,
    mut v_autoSpecialize_3240_: *mut leanh::LeanObject,
    mut v___x_3241_: *mut leanh::LeanObject,
    mut v___x_3242_: *mut leanh::LeanObject,
    mut v_a_3243_: *mut leanh::LeanObject,
    mut v_b_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
    mut v___y_3248_: *mut leanh::LeanObject,
    mut v___y_3249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3250_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v_upperBound_3238_, v___x_3239_, v_autoSpecialize_3240_, v___x_3241_, v___x_3242_, v_a_3243_, v_b_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
    leanh::lean_dec(v___y_3248_);
    leanh::lean_dec_ref(v___y_3247_);
    leanh::lean_dec(v___y_3246_);
    leanh::lean_dec_ref(v___y_3245_);
    leanh::lean_dec_ref(v___x_3239_);
    leanh::lean_dec(v_upperBound_3238_);
    return v_res_3250_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(
    mut v_autoSpecialize_3251_: *mut leanh::LeanObject,
    mut v_as_3252_: *mut leanh::LeanObject,
    mut v_sz_3253_: usize,
    mut v_i_3254_: usize,
    mut v_b_3255_: *mut leanh::LeanObject,
    mut v___y_3256_: *mut leanh::LeanObject,
    mut v___y_3257_: *mut leanh::LeanObject,
    mut v___y_3258_: *mut leanh::LeanObject,
    mut v___y_3259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: usize = 0;
    let mut v___x_3264_: usize = 0;
    let mut v___x_3266_: u8 = 0;
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: u8 = 0;
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3266_ = lean_usize_dec_lt(v_i_3254_, v_sz_3253_);
                if v___x_3266_ == 0 {
                    leanh::lean_dec_ref(v_autoSpecialize_3251_);
                    v___x_3267_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3267_, 0, v_b_3255_);
                    return v___x_3267_;
                } else {
                    v___x_3268_ = lean_st_ref_get(v___y_3259_);
                    v_env_3269_ = leanh::lean_ctor_get(v___x_3268_, 0);
                    leanh::lean_inc_ref(v_env_3269_);
                    leanh::lean_dec(v___x_3268_);
                    v_a_3270_ = lean_array_uget_borrowed(v_as_3252_, v_i_3254_);
                    v_toSignature_3271_ = leanh::lean_ctor_get(v_a_3270_, 0);
                    v_name_3272_ = leanh::lean_ctor_get(v_toSignature_3271_, 0);
                    v_params_3273_ = leanh::lean_ctor_get(v_toSignature_3271_, 3);
                    leanh::lean_inc(v_name_3272_);
                    v___x_3274_ =
                        l_Lean_Compiler_hasNospecializeAttribute(v_env_3269_, v_name_3272_);
                    if v___x_3274_ == 0 {
                        v___x_3275_ = lean_st_ref_get(v___y_3259_);
                        v_env_3276_ = leanh::lean_ctor_get(v___x_3275_, 0);
                        leanh::lean_inc_ref(v_env_3276_);
                        leanh::lean_dec(v___x_3275_);
                        v___x_3277_ = lean_array_get_size(v_params_3273_);
                        v___x_3278_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3279_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
                        leanh::lean_inc_n(v_name_3272_, 2);
                        v___x_3280_ =
                            l_Lean_Compiler_getSpecializationArgs_x3f(v_env_3276_, v_name_3272_);
                        leanh::lean_inc_ref(v_autoSpecialize_3251_);
                        v___x_3281_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v___x_3277_, v_params_3273_, v_autoSpecialize_3251_, v_name_3272_, v___x_3280_, v___x_3278_, v___x_3279_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
                        if leanh::lean_obj_tag(v___x_3281_) == 0 {
                            v_a_3282_ = leanh::lean_ctor_get(v___x_3281_, 0);
                            leanh::lean_inc(v_a_3282_);
                            leanh::lean_dec_ref_known(v___x_3281_, 1);
                            v___x_3283_ = lean_array_push(v_b_3255_, v_a_3282_);
                            v_a_3262_ = v___x_3283_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_3255_);
                            leanh::lean_dec_ref(v_autoSpecialize_3251_);
                            v_a_3284_ = leanh::lean_ctor_get(v___x_3281_, 0);
                            v_isSharedCheck_3291_ =
                                (!leanh::lean_is_exclusive(v___x_3281_)) as u8;
                            if v_isSharedCheck_3291_ == 0 {
                                v___x_3286_ = v___x_3281_;
                                v_isShared_3287_ = v_isSharedCheck_3291_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3284_);
                                leanh::lean_dec(v___x_3281_);
                                v___x_3286_ = leanh::lean_box(0);
                                v_isShared_3287_ = v_isSharedCheck_3291_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v___x_3292_ = lean_array_get_size(v_params_3273_);
                        v___x_3293_ = leanh::lean_box(4);
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
                    v_reuseFailAlloc_3290_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
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
    mut v_autoSpecialize_3296_: *mut leanh::LeanObject,
    mut v_as_3297_: *mut leanh::LeanObject,
    mut v_sz_3298_: *mut leanh::LeanObject,
    mut v_i_3299_: *mut leanh::LeanObject,
    mut v_b_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
    mut v___y_3302_: *mut leanh::LeanObject,
    mut v___y_3303_: *mut leanh::LeanObject,
    mut v___y_3304_: *mut leanh::LeanObject,
    mut v___y_3305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3306_: usize = 0;
    let mut v_i_boxed_3307_: usize = 0;
    let mut v_res_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3306_ = leanh::lean_unbox_usize(v_sz_3298_);
    leanh::lean_dec(v_sz_3298_);
    v_i_boxed_3307_ = leanh::lean_unbox_usize(v_i_3299_);
    leanh::lean_dec(v_i_3299_);
    v_res_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_3296_, v_as_3297_, v_sz_boxed_3306_, v_i_boxed_3307_, v_b_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
    leanh::lean_dec(v___y_3304_);
    leanh::lean_dec_ref(v___y_3303_);
    leanh::lean_dec(v___y_3302_);
    leanh::lean_dec_ref(v___y_3301_);
    leanh::lean_dec_ref(v_as_3297_);
    return v_res_3308_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(
    mut v_as_3309_: *mut leanh::LeanObject,
    mut v_i_3310_: usize,
    mut v_stop_3311_: usize,
) -> u8 {
    let mut v___x_3312_: u8 = 0;
    let mut v___x_3313_: u8 = 0;
    let mut v___y_3315_: u8 = 0;
    let mut v___x_3316_: usize = 0;
    let mut v___x_3317_: usize = 0;
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    match leanh::lean_obj_tag(v___x_3319_) {
                        0 => {
                            v_weak_3320_ = leanh::lean_ctor_get_uint8(v___x_3319_, 0 as u32);
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
    mut v_as_3322_: *mut leanh::LeanObject,
    mut v_i_3323_: *mut leanh::LeanObject,
    mut v_stop_3324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3325_: usize = 0;
    let mut v_stop_boxed_3326_: usize = 0;
    let mut v_res_3327_: u8 = 0;
    let mut v_r_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3325_ = leanh::lean_unbox_usize(v_i_3323_);
    leanh::lean_dec(v_i_3323_);
    v_stop_boxed_3326_ = leanh::lean_unbox_usize(v_stop_3324_);
    leanh::lean_dec(v_stop_3324_);
    v_res_3327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__2(v_as_3322_, v_i_boxed_3325_, v_stop_boxed_3326_);
    leanh::lean_dec_ref(v_as_3322_);
    v_r_3328_ = leanh::lean_box((v_res_3327_) as usize);
    return v_r_3328_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(
    mut v_as_3329_: *mut leanh::LeanObject,
    mut v_i_3330_: usize,
    mut v_stop_3331_: usize,
) -> u8 {
    let mut v___x_3332_: u8 = 0;
    let mut v___x_3333_: u8 = 0;
    let mut v___y_3335_: u8 = 0;
    let mut v___x_3336_: usize = 0;
    let mut v___x_3337_: usize = 0;
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    v___x_3340_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_as_3347_: *mut leanh::LeanObject,
    mut v_i_3348_: *mut leanh::LeanObject,
    mut v_stop_3349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3350_: usize = 0;
    let mut v_stop_boxed_3351_: usize = 0;
    let mut v_res_3352_: u8 = 0;
    let mut v_r_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3350_ = leanh::lean_unbox_usize(v_i_3348_);
    leanh::lean_dec(v_i_3348_);
    v_stop_boxed_3351_ = leanh::lean_unbox_usize(v_stop_3349_);
    leanh::lean_dec(v_stop_3349_);
    v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_as_3347_, v_i_boxed_3350_, v_stop_boxed_3351_);
    leanh::lean_dec_ref(v_as_3347_);
    v_r_3353_ = leanh::lean_box((v_res_3352_) as usize);
    return v_r_3353_;
}
pub unsafe fn l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(
    mut v_as_3354_: *mut leanh::LeanObject,
    mut v_bs_3355_: *mut leanh::LeanObject,
    mut v_i_3356_: *mut leanh::LeanObject,
    mut v_cs_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: u8 = 0;
    let mut v_a_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: u8 = 0;
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3364_ = lean_array_get_size(v_as_3354_);
                v___x_3365_ = lean_nat_dec_lt(v_i_3356_, v___x_3364_);
                if v___x_3365_ == 0 {
                    leanh::lean_dec(v_i_3356_);
                    return v_cs_3357_;
                } else {
                    v___x_3366_ = lean_array_get_size(v_bs_3355_);
                    v___x_3367_ = lean_nat_dec_lt(v_i_3356_, v___x_3366_);
                    if v___x_3367_ == 0 {
                        leanh::lean_dec(v_i_3356_);
                        return v_cs_3357_;
                    } else {
                        v_a_3368_ = lean_array_fget_borrowed(v_as_3354_, v_i_3356_);
                        v_b_3369_ = lean_array_fget_borrowed(v_bs_3355_, v_i_3356_);
                        v___x_3370_ = (leanh::lean_unbox(v_b_3369_) as u8);
                        if v___x_3370_ == 0 {
                            if leanh::lean_obj_tag(v_a_3368_) == 3 {
                                v___y_3359_ = v_a_3368_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3371_ = leanh::lean_box(4);
                                v___y_3359_ = v___x_3371_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_inc(v_a_3368_);
                            v___y_3359_ = v_a_3368_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3360_ = leanh::lean_unsigned_to_nat(1);
                v___x_3361_ = lean_nat_add(v_i_3356_, v___x_3360_);
                leanh::lean_dec(v_i_3356_);
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
    mut v_as_3372_: *mut leanh::LeanObject,
    mut v_bs_3373_: *mut leanh::LeanObject,
    mut v_i_3374_: *mut leanh::LeanObject,
    mut v_cs_3375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3376_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(
        v_as_3372_, v_bs_3373_, v_i_3374_, v_cs_3375_,
    );
    leanh::lean_dec_ref(v_bs_3373_);
    leanh::lean_dec_ref(v_as_3372_);
    return v_res_3376_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(
    mut v_upperBound_3377_: *mut leanh::LeanObject,
    mut v___x_3378_: *mut leanh::LeanObject,
    mut v_a_3379_: *mut leanh::LeanObject,
    mut v_b_3380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3387_ = lean_nat_dec_lt(v_a_3379_, v_upperBound_3377_);
                if v___x_3387_ == 0 {
                    leanh::lean_dec(v_a_3379_);
                    v___x_3388_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3388_, 0, v_b_3380_);
                    return v___x_3388_;
                } else {
                    v___x_3389_ = l_Lean_Compiler_LCNF_instInhabitedSpecParamInfo_default;
                    v___x_3390_ = lean_array_get_borrowed(v___x_3389_, v_b_3380_, v_a_3379_);
                    if leanh::lean_obj_tag(v___x_3390_) == 2 {
                        v___x_3391_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_hasFwdDeps(v___x_3378_, v_b_3380_, v_a_3379_);
                        if v___x_3391_ == 0 {
                            v___x_3392_ = leanh::lean_box(4);
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
                v___x_3384_ = leanh::lean_unsigned_to_nat(1);
                v___x_3385_ = lean_nat_add(v_a_3379_, v___x_3384_);
                leanh::lean_dec(v_a_3379_);
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
    mut v_upperBound_3394_: *mut leanh::LeanObject,
    mut v___x_3395_: *mut leanh::LeanObject,
    mut v_a_3396_: *mut leanh::LeanObject,
    mut v_b_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3399_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_3394_, v___x_3395_, v_a_3396_, v_b_3397_);
    leanh::lean_dec_ref(v___x_3395_);
    leanh::lean_dec(v_upperBound_3394_);
    return v_res_3399_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_3400_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__3;
    v___x_3405_ = leanh::lean_unsigned_to_nat(43);
    v___x_3406_ = leanh::lean_unsigned_to_nat(236);
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
    mut v_upperBound_3410_: *mut leanh::LeanObject,
    mut v_decls_3411_: *mut leanh::LeanObject,
    mut v_alreadySpecialized_3412_: *mut leanh::LeanObject,
    mut v___x_3413_: *mut leanh::LeanObject,
    mut v_a_3414_: *mut leanh::LeanObject,
    mut v_a_3415_: *mut leanh::LeanObject,
    mut v_b_3416_: *mut leanh::LeanObject,
    mut v___y_3417_: *mut leanh::LeanObject,
    mut v___y_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
    mut v___y_3420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3461_: u8 = 0;
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3427_ = lean_nat_dec_lt(v_a_3415_, v_upperBound_3410_);
                if v___x_3427_ == 0 {
                    leanh::lean_dec(v_a_3415_);
                    v___x_3428_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3428_, 0, v_b_3416_);
                    return v___x_3428_;
                } else {
                    v___x_3429_ = lean_array_fget_borrowed(v_decls_3411_, v_a_3415_);
                    v_toSignature_3430_ = leanh::lean_ctor_get(v___x_3429_, 0);
                    v_name_3431_ = leanh::lean_ctor_get(v_toSignature_3430_, 0);
                    v___x_3432_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3413_, v_name_3431_);
                    if leanh::lean_obj_tag(v___x_3432_) == 1 {
                        v_val_3433_ = leanh::lean_ctor_get(v___x_3432_, 0);
                        leanh::lean_inc(v_val_3433_);
                        leanh::lean_dec_ref_known(v___x_3432_, 1);
                        v___x_3434_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__0);
                        v___x_3435_ = lean_array_get_borrowed(v___x_3434_, v_a_3414_, v_a_3415_);
                        v___x_3436_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3437_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
                        v___x_3438_ = l_Array_zipWithMAux___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__6(v___x_3435_, v_val_3433_, v___x_3436_, v___x_3437_);
                        leanh::lean_dec(v_val_3433_);
                        v___x_3439_ = lean_array_get_size(v___x_3438_);
                        v___x_3440_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v___x_3439_, v___x_3429_, v___x_3436_, v___x_3438_);
                        if leanh::lean_obj_tag(v___x_3440_) == 0 {
                            v_a_3441_ = leanh::lean_ctor_get(v___x_3440_, 0);
                            leanh::lean_inc(v_a_3441_);
                            leanh::lean_dec_ref_known(v___x_3440_, 1);
                            v___x_3442_ = 0;
                            v___x_3443_ = leanh::lean_box((v___x_3442_) as usize);
                            v___x_3444_ =
                                lean_array_get(v___x_3443_, v_alreadySpecialized_3412_, v_a_3415_);
                            leanh::lean_dec(v___x_3443_);
                            leanh::lean_inc(v_name_3431_);
                            v___x_3445_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            leanh::lean_ctor_set(v___x_3445_, 0, v_name_3431_);
                            leanh::lean_ctor_set(v___x_3445_, 1, v_a_3441_);
                            v___x_3446_ = (leanh::lean_unbox(v___x_3444_) as u8);
                            leanh::lean_dec(v___x_3444_);
                            leanh::lean_ctor_set_uint8(
                                v___x_3445_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                                v___x_3446_,
                            );
                            v___x_3447_ = lean_array_push(v_b_3416_, v___x_3445_);
                            v_a_3423_ = v___x_3447_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_3416_);
                            leanh::lean_dec(v_a_3415_);
                            v_a_3448_ = leanh::lean_ctor_get(v___x_3440_, 0);
                            v_isSharedCheck_3455_ =
                                (!leanh::lean_is_exclusive(v___x_3440_)) as u8;
                            if v_isSharedCheck_3455_ == 0 {
                                v___x_3450_ = v___x_3440_;
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3448_);
                                leanh::lean_dec(v___x_3440_);
                                v___x_3450_ = leanh::lean_box(0);
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3432_);
                        v___x_3456_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg___closed__4);
                        v___x_3457_ =
                            l_panic___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__8(
                                v___x_3456_,
                                v___y_3417_,
                                v___y_3418_,
                                v___y_3419_,
                                v___y_3420_,
                            );
                        if leanh::lean_obj_tag(v___x_3457_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3457_, 1);
                            v_a_3423_ = v_b_3416_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_3416_);
                            leanh::lean_dec(v_a_3415_);
                            v_a_3458_ = leanh::lean_ctor_get(v___x_3457_, 0);
                            v_isSharedCheck_3465_ =
                                (!leanh::lean_is_exclusive(v___x_3457_)) as u8;
                            if v_isSharedCheck_3465_ == 0 {
                                v___x_3460_ = v___x_3457_;
                                v_isShared_3461_ = v_isSharedCheck_3465_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3458_);
                                leanh::lean_dec(v___x_3457_);
                                v___x_3460_ = leanh::lean_box(0);
                                v_isShared_3461_ = v_isSharedCheck_3465_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3424_ = leanh::lean_unsigned_to_nat(1);
                v___x_3425_ = lean_nat_add(v_a_3415_, v___x_3424_);
                leanh::lean_dec(v_a_3415_);
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
                    v_reuseFailAlloc_3454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
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
                    v_reuseFailAlloc_3464_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
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
    mut v_upperBound_3466_: *mut leanh::LeanObject,
    mut v_decls_3467_: *mut leanh::LeanObject,
    mut v_alreadySpecialized_3468_: *mut leanh::LeanObject,
    mut v___x_3469_: *mut leanh::LeanObject,
    mut v_a_3470_: *mut leanh::LeanObject,
    mut v_a_3471_: *mut leanh::LeanObject,
    mut v_b_3472_: *mut leanh::LeanObject,
    mut v___y_3473_: *mut leanh::LeanObject,
    mut v___y_3474_: *mut leanh::LeanObject,
    mut v___y_3475_: *mut leanh::LeanObject,
    mut v___y_3476_: *mut leanh::LeanObject,
    mut v___y_3477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3478_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_3466_, v_decls_3467_, v_alreadySpecialized_3468_, v___x_3469_, v_a_3470_, v_a_3471_, v_b_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
    leanh::lean_dec(v___y_3476_);
    leanh::lean_dec_ref(v___y_3475_);
    leanh::lean_dec(v___y_3474_);
    leanh::lean_dec_ref(v___y_3473_);
    leanh::lean_dec_ref(v_a_3470_);
    leanh::lean_dec(v___x_3469_);
    leanh::lean_dec_ref(v_alreadySpecialized_3468_);
    leanh::lean_dec_ref(v_decls_3467_);
    leanh::lean_dec(v_upperBound_3466_);
    return v_res_3478_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(
    mut v_alreadySpecialized_3479_: *mut leanh::LeanObject,
    mut v_as_3480_: *mut leanh::LeanObject,
    mut v_i_3481_: *mut leanh::LeanObject,
    mut v_j_3482_: *mut leanh::LeanObject,
    mut v_bs_3483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3485_: u8 = 0;
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3484_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3485_ = lean_nat_dec_eq(v_i_3481_, v_zero_3484_);
                if v_isZero_3485_ == 1 {
                    leanh::lean_dec(v_j_3482_);
                    leanh::lean_dec(v_i_3481_);
                    return v_bs_3483_;
                } else {
                    v___x_3486_ = lean_array_fget_borrowed(v_as_3480_, v_j_3482_);
                    v_toSignature_3487_ = leanh::lean_ctor_get(v___x_3486_, 0);
                    v_name_3488_ = leanh::lean_ctor_get(v_toSignature_3487_, 0);
                    v_params_3489_ = leanh::lean_ctor_get(v_toSignature_3487_, 3);
                    v_one_3490_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3491_ = lean_nat_sub(v_i_3481_, v_one_3490_);
                    leanh::lean_dec(v_i_3481_);
                    v___x_3492_ = lean_array_get_size(v_params_3489_);
                    v___x_3493_ = leanh::lean_box(4);
                    v___x_3494_ = lean_mk_array(v___x_3492_, v___x_3493_);
                    v___x_3495_ = leanh::lean_box((v_isZero_3485_) as usize);
                    v___x_3496_ =
                        lean_array_get(v___x_3495_, v_alreadySpecialized_3479_, v_j_3482_);
                    leanh::lean_dec(v___x_3495_);
                    leanh::lean_inc(v_name_3488_);
                    v___x_3497_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_3497_, 0, v_name_3488_);
                    leanh::lean_ctor_set(v___x_3497_, 1, v___x_3494_);
                    v___x_3498_ = (leanh::lean_unbox(v___x_3496_) as u8);
                    leanh::lean_dec(v___x_3496_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3497_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_3498_,
                    );
                    v___x_3499_ = lean_nat_add(v_j_3482_, v_one_3490_);
                    leanh::lean_dec(v_j_3482_);
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
    mut v_alreadySpecialized_3502_: *mut leanh::LeanObject,
    mut v_as_3503_: *mut leanh::LeanObject,
    mut v_i_3504_: *mut leanh::LeanObject,
    mut v_j_3505_: *mut leanh::LeanObject,
    mut v_bs_3506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3507_ =
        l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(
            v_alreadySpecialized_3502_,
            v_as_3503_,
            v_i_3504_,
            v_j_3505_,
            v_bs_3506_,
        );
    leanh::lean_dec_ref(v_as_3503_);
    leanh::lean_dec_ref(v_alreadySpecialized_3502_);
    return v_res_3507_;
}
pub unsafe fn l_Lean_Compiler_LCNF_computeSpecEntries(
    mut v_decls_3510_: *mut leanh::LeanObject,
    mut v_autoSpecialize_3511_: *mut leanh::LeanObject,
    mut v_alreadySpecialized_3512_: *mut leanh::LeanObject,
    mut v_a_3513_: *mut leanh::LeanObject,
    mut v_a_3514_: *mut leanh::LeanObject,
    mut v_a_3515_: *mut leanh::LeanObject,
    mut v_a_3516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declsInfo_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3520_: usize = 0;
    let mut v___x_3521_: usize = 0;
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: u8 = 0;
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v_a_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3546_: u8 = 0;
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3518_ = leanh::lean_unsigned_to_nat(0);
                v_declsInfo_3519_ = l_Lean_Compiler_LCNF_computeSpecEntries___closed__0;
                v_sz_3520_ = lean_array_size(v_decls_3510_);
                v___x_3521_ = 0usize;
                v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__3(v_autoSpecialize_3511_, v_decls_3510_, v_sz_3520_, v___x_3521_, v_declsInfo_3519_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
                if leanh::lean_obj_tag(v___x_3522_) == 0 {
                    v_a_3523_ = leanh::lean_ctor_get(v___x_3522_, 0);
                    v_isSharedCheck_3542_ = (!leanh::lean_is_exclusive(v___x_3522_)) as u8;
                    if v_isSharedCheck_3542_ == 0 {
                        v___x_3525_ = v___x_3522_;
                        v_isShared_3526_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3523_);
                        leanh::lean_dec(v___x_3522_);
                        v___x_3525_ = leanh::lean_box(0);
                        v_isShared_3526_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_decls_3510_);
                    v_a_3543_ = leanh::lean_ctor_get(v___x_3522_, 0);
                    v_isSharedCheck_3550_ = (!leanh::lean_is_exclusive(v___x_3522_)) as u8;
                    if v_isSharedCheck_3550_ == 0 {
                        v___x_3545_ = v___x_3522_;
                        v_isShared_3546_ = v_isSharedCheck_3550_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3543_);
                        leanh::lean_dec(v___x_3522_);
                        v___x_3545_ = leanh::lean_box(0);
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
                    leanh::lean_dec(v_a_3523_);
                    state = 2;
                    continue;
                } else {
                    if v___x_3535_ == 0 {
                        leanh::lean_dec(v_a_3523_);
                        state = 2;
                        continue;
                    } else {
                        v___x_3536_ = lean_usize_of_nat(v___x_3534_);
                        v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__5(v_a_3523_, v___x_3521_, v___x_3536_);
                        if v___x_3537_ == 0 {
                            leanh::lean_dec(v_a_3523_);
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_3525_);
                            v___x_3538_ = lean_array_get_size(v_decls_3510_);
                            v___x_3539_ = lean_mk_empty_array_with_capacity(v___x_3538_);
                            leanh::lean_inc_ref(v_decls_3510_);
                            v___x_3540_ = l_Lean_Compiler_LCNF_mkFixedParamsMap(v_decls_3510_);
                            v___x_3541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v___x_3538_, v_decls_3510_, v_alreadySpecialized_3512_, v___x_3540_, v_a_3523_, v___x_3518_, v___x_3539_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
                            leanh::lean_dec(v_a_3523_);
                            leanh::lean_dec(v___x_3540_);
                            leanh::lean_dec_ref(v_decls_3510_);
                            return v___x_3541_;
                        }
                    }
                }
            }
            2 => {
                v___x_3528_ = lean_array_get_size(v_decls_3510_);
                v___x_3529_ = lean_mk_empty_array_with_capacity(v___x_3528_);
                v___x_3530_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4___redArg(v_alreadySpecialized_3512_, v_decls_3510_, v___x_3528_, v___x_3518_, v___x_3529_);
                leanh::lean_dec_ref(v_decls_3510_);
                if v_isShared_3526_ == 0 {
                    leanh::lean_ctor_set(v___x_3525_, 0, v___x_3530_);
                    v___x_3532_ = v___x_3525_;
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
            3 => {
                return v___x_3532_;
            }
            4 => {
                if v_isShared_3546_ == 0 {
                    v___x_3548_ = v___x_3545_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3549_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
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
    mut v_decls_3551_: *mut leanh::LeanObject,
    mut v_autoSpecialize_3552_: *mut leanh::LeanObject,
    mut v_alreadySpecialized_3553_: *mut leanh::LeanObject,
    mut v_a_3554_: *mut leanh::LeanObject,
    mut v_a_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
    mut v_a_3557_: *mut leanh::LeanObject,
    mut v_a_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Lean_Compiler_LCNF_computeSpecEntries(
        v_decls_3551_,
        v_autoSpecialize_3552_,
        v_alreadySpecialized_3553_,
        v_a_3554_,
        v_a_3555_,
        v_a_3556_,
        v_a_3557_,
    );
    leanh::lean_dec(v_a_3557_);
    leanh::lean_dec_ref(v_a_3556_);
    leanh::lean_dec(v_a_3555_);
    leanh::lean_dec_ref(v_a_3554_);
    leanh::lean_dec_ref(v_alreadySpecialized_3553_);
    return v_res_3559_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1(
    mut v_upperBound_3560_: *mut leanh::LeanObject,
    mut v___x_3561_: *mut leanh::LeanObject,
    mut v_autoSpecialize_3562_: *mut leanh::LeanObject,
    mut v___x_3563_: *mut leanh::LeanObject,
    mut v___x_3564_: *mut leanh::LeanObject,
    mut v_inst_3565_: *mut leanh::LeanObject,
    mut v_R_3566_: *mut leanh::LeanObject,
    mut v_a_3567_: *mut leanh::LeanObject,
    mut v_b_3568_: *mut leanh::LeanObject,
    mut v_c_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
    mut v___y_3572_: *mut leanh::LeanObject,
    mut v___y_3573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3575_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___redArg(v_upperBound_3560_, v___x_3561_, v_autoSpecialize_3562_, v___x_3563_, v___x_3564_, v_a_3567_, v_b_3568_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
    return v___x_3575_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__1___boxed(
    mut v_upperBound_3576_: *mut leanh::LeanObject,
    mut v___x_3577_: *mut leanh::LeanObject,
    mut v_autoSpecialize_3578_: *mut leanh::LeanObject,
    mut v___x_3579_: *mut leanh::LeanObject,
    mut v___x_3580_: *mut leanh::LeanObject,
    mut v_inst_3581_: *mut leanh::LeanObject,
    mut v_R_3582_: *mut leanh::LeanObject,
    mut v_a_3583_: *mut leanh::LeanObject,
    mut v_b_3584_: *mut leanh::LeanObject,
    mut v_c_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3589_);
    leanh::lean_dec_ref(v___y_3588_);
    leanh::lean_dec(v___y_3587_);
    leanh::lean_dec_ref(v___y_3586_);
    leanh::lean_dec_ref(v___x_3577_);
    leanh::lean_dec(v_upperBound_3576_);
    return v_res_3591_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(
    mut v_alreadySpecialized_3592_: *mut leanh::LeanObject,
    mut v_as_3593_: *mut leanh::LeanObject,
    mut v_i_3594_: *mut leanh::LeanObject,
    mut v_j_3595_: *mut leanh::LeanObject,
    mut v_inv_3596_: *mut leanh::LeanObject,
    mut v_bs_3597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_alreadySpecialized_3599_: *mut leanh::LeanObject,
    mut v_as_3600_: *mut leanh::LeanObject,
    mut v_i_3601_: *mut leanh::LeanObject,
    mut v_j_3602_: *mut leanh::LeanObject,
    mut v_inv_3603_: *mut leanh::LeanObject,
    mut v_bs_3604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3605_ = l_Array_mapFinIdxM_map___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__4(
        v_alreadySpecialized_3599_,
        v_as_3600_,
        v_i_3601_,
        v_j_3602_,
        v_inv_3603_,
        v_bs_3604_,
    );
    leanh::lean_dec_ref(v_as_3600_);
    leanh::lean_dec_ref(v_alreadySpecialized_3599_);
    return v_res_3605_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7(
    mut v_upperBound_3606_: *mut leanh::LeanObject,
    mut v___x_3607_: *mut leanh::LeanObject,
    mut v_inst_3608_: *mut leanh::LeanObject,
    mut v_R_3609_: *mut leanh::LeanObject,
    mut v_a_3610_: *mut leanh::LeanObject,
    mut v_b_3611_: *mut leanh::LeanObject,
    mut v_c_3612_: *mut leanh::LeanObject,
    mut v___y_3613_: *mut leanh::LeanObject,
    mut v___y_3614_: *mut leanh::LeanObject,
    mut v___y_3615_: *mut leanh::LeanObject,
    mut v___y_3616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3618_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___redArg(v_upperBound_3606_, v___x_3607_, v_a_3610_, v_b_3611_);
    return v___x_3618_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__7___boxed(
    mut v_upperBound_3619_: *mut leanh::LeanObject,
    mut v___x_3620_: *mut leanh::LeanObject,
    mut v_inst_3621_: *mut leanh::LeanObject,
    mut v_R_3622_: *mut leanh::LeanObject,
    mut v_a_3623_: *mut leanh::LeanObject,
    mut v_b_3624_: *mut leanh::LeanObject,
    mut v_c_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
    mut v___y_3627_: *mut leanh::LeanObject,
    mut v___y_3628_: *mut leanh::LeanObject,
    mut v___y_3629_: *mut leanh::LeanObject,
    mut v___y_3630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3629_);
    leanh::lean_dec_ref(v___y_3628_);
    leanh::lean_dec(v___y_3627_);
    leanh::lean_dec_ref(v___y_3626_);
    leanh::lean_dec_ref(v___x_3620_);
    leanh::lean_dec(v_upperBound_3619_);
    return v_res_3631_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9(
    mut v_upperBound_3632_: *mut leanh::LeanObject,
    mut v_decls_3633_: *mut leanh::LeanObject,
    mut v_alreadySpecialized_3634_: *mut leanh::LeanObject,
    mut v___x_3635_: *mut leanh::LeanObject,
    mut v_a_3636_: *mut leanh::LeanObject,
    mut v_inst_3637_: *mut leanh::LeanObject,
    mut v_R_3638_: *mut leanh::LeanObject,
    mut v_a_3639_: *mut leanh::LeanObject,
    mut v_b_3640_: *mut leanh::LeanObject,
    mut v_c_3641_: *mut leanh::LeanObject,
    mut v___y_3642_: *mut leanh::LeanObject,
    mut v___y_3643_: *mut leanh::LeanObject,
    mut v___y_3644_: *mut leanh::LeanObject,
    mut v___y_3645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3647_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___redArg(v_upperBound_3632_, v_decls_3633_, v_alreadySpecialized_3634_, v___x_3635_, v_a_3636_, v_a_3639_, v_b_3640_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
    return v___x_3647_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_computeSpecEntries_spec__9___boxed(
    mut v_upperBound_3648_: *mut leanh::LeanObject,
    mut v_decls_3649_: *mut leanh::LeanObject,
    mut v_alreadySpecialized_3650_: *mut leanh::LeanObject,
    mut v___x_3651_: *mut leanh::LeanObject,
    mut v_a_3652_: *mut leanh::LeanObject,
    mut v_inst_3653_: *mut leanh::LeanObject,
    mut v_R_3654_: *mut leanh::LeanObject,
    mut v_a_3655_: *mut leanh::LeanObject,
    mut v_b_3656_: *mut leanh::LeanObject,
    mut v_c_3657_: *mut leanh::LeanObject,
    mut v___y_3658_: *mut leanh::LeanObject,
    mut v___y_3659_: *mut leanh::LeanObject,
    mut v___y_3660_: *mut leanh::LeanObject,
    mut v___y_3661_: *mut leanh::LeanObject,
    mut v___y_3662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3661_);
    leanh::lean_dec_ref(v___y_3660_);
    leanh::lean_dec(v___y_3659_);
    leanh::lean_dec_ref(v___y_3658_);
    leanh::lean_dec_ref(v_a_3652_);
    leanh::lean_dec(v___x_3651_);
    leanh::lean_dec_ref(v_alreadySpecialized_3650_);
    leanh::lean_dec_ref(v_decls_3649_);
    leanh::lean_dec(v_upperBound_3648_);
    return v_res_3663_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3664_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3664_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__0,
    );
    v___x_3666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3666_, 0, v___x_3665_);
    return v___x_3666_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3667_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__1,
    );
    v___x_3668_ = leanh::lean_unsigned_to_nat(0);
    v___x_3669_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3669_, 0, v___x_3668_);
    leanh::lean_ctor_set(v___x_3669_, 1, v___x_3668_);
    leanh::lean_ctor_set(v___x_3669_, 2, v___x_3668_);
    leanh::lean_ctor_set(v___x_3669_, 3, v___x_3668_);
    leanh::lean_ctor_set(v___x_3669_, 4, v___x_3667_);
    leanh::lean_ctor_set(v___x_3669_, 5, v___x_3667_);
    leanh::lean_ctor_set(v___x_3669_, 6, v___x_3667_);
    leanh::lean_ctor_set(v___x_3669_, 7, v___x_3667_);
    leanh::lean_ctor_set(v___x_3669_, 8, v___x_3667_);
    leanh::lean_ctor_set(v___x_3669_, 9, v___x_3667_);
    return v___x_3669_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3()
-> f64 {
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: f64 = 0.0;
    v___x_3670_ = leanh::lean_unsigned_to_nat(0);
    v___x_3671_ = lean_float_of_nat(v___x_3670_);
    return v___x_3671_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(
    mut v_cls_3675_: *mut leanh::LeanObject,
    mut v_msg_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v_env_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3709_: u8 = 0;
    let mut v_tid_3710_: u64 = 0;
    let mut v_traces_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3715_: u8 = 0;
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: f64 = 0.0;
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3741_: u8 = 0;
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v_unused_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v_a_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3682_ = leanh::lean_ctor_get(v___y_3679_, 2);
                v_ref_3683_ = leanh::lean_ctor_get(v___y_3679_, 5);
                v___x_3684_ = lean_st_ref_get(v___y_3680_);
                v___x_3685_ = lean_st_ref_get(v___y_3678_);
                v___x_3686_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3677_);
                if leanh::lean_obj_tag(v___x_3686_) == 0 {
                    v_a_3687_ = leanh::lean_ctor_get(v___x_3686_, 0);
                    v_isSharedCheck_3745_ = (!leanh::lean_is_exclusive(v___x_3686_)) as u8;
                    if v_isSharedCheck_3745_ == 0 {
                        v___x_3689_ = v___x_3686_;
                        v_isShared_3690_ = v_isSharedCheck_3745_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3687_);
                        leanh::lean_dec(v___x_3686_);
                        v___x_3689_ = leanh::lean_box(0);
                        v_isShared_3690_ = v_isSharedCheck_3745_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3685_);
                    leanh::lean_dec(v___x_3684_);
                    leanh::lean_dec_ref(v_msg_3676_);
                    leanh::lean_dec(v_cls_3675_);
                    v_a_3746_ = leanh::lean_ctor_get(v___x_3686_, 0);
                    v_isSharedCheck_3753_ = (!leanh::lean_is_exclusive(v___x_3686_)) as u8;
                    if v_isSharedCheck_3753_ == 0 {
                        v___x_3748_ = v___x_3686_;
                        v_isShared_3749_ = v_isSharedCheck_3753_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3746_);
                        leanh::lean_dec(v___x_3686_);
                        v___x_3748_ = leanh::lean_box(0);
                        v_isShared_3749_ = v_isSharedCheck_3753_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3691_ = leanh::lean_ctor_get(v___x_3684_, 0);
                leanh::lean_inc_ref(v_env_3691_);
                leanh::lean_dec(v___x_3684_);
                v_lctx_3692_ = leanh::lean_ctor_get(v___x_3685_, 0);
                v_isSharedCheck_3743_ = (!leanh::lean_is_exclusive(v___x_3685_)) as u8;
                if v_isSharedCheck_3743_ == 0 {
                    v_unused_3744_ = leanh::lean_ctor_get(v___x_3685_, 1);
                    leanh::lean_dec(v_unused_3744_);
                    v___x_3694_ = v___x_3685_;
                    v_isShared_3695_ = v_isSharedCheck_3743_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lctx_3692_);
                    leanh::lean_dec(v___x_3685_);
                    v___x_3694_ = leanh::lean_box(0);
                    v_isShared_3695_ = v_isSharedCheck_3743_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3696_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__2);
                v___x_3697_ = lean_st_ref_take(v___y_3680_);
                v_traceState_3698_ = leanh::lean_ctor_get(v___x_3697_, 4);
                v_env_3699_ = leanh::lean_ctor_get(v___x_3697_, 0);
                v_nextMacroScope_3700_ = leanh::lean_ctor_get(v___x_3697_, 1);
                v_ngen_3701_ = leanh::lean_ctor_get(v___x_3697_, 2);
                v_auxDeclNGen_3702_ = leanh::lean_ctor_get(v___x_3697_, 3);
                v_cache_3703_ = leanh::lean_ctor_get(v___x_3697_, 5);
                v_messages_3704_ = leanh::lean_ctor_get(v___x_3697_, 6);
                v_infoState_3705_ = leanh::lean_ctor_get(v___x_3697_, 7);
                v_snapshotTasks_3706_ = leanh::lean_ctor_get(v___x_3697_, 8);
                v_isSharedCheck_3742_ = (!leanh::lean_is_exclusive(v___x_3697_)) as u8;
                if v_isSharedCheck_3742_ == 0 {
                    v___x_3708_ = v___x_3697_;
                    v_isShared_3709_ = v_isSharedCheck_3742_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3706_);
                    leanh::lean_inc(v_infoState_3705_);
                    leanh::lean_inc(v_messages_3704_);
                    leanh::lean_inc(v_cache_3703_);
                    leanh::lean_inc(v_traceState_3698_);
                    leanh::lean_inc(v_auxDeclNGen_3702_);
                    leanh::lean_inc(v_ngen_3701_);
                    leanh::lean_inc(v_nextMacroScope_3700_);
                    leanh::lean_inc(v_env_3699_);
                    leanh::lean_dec(v___x_3697_);
                    v___x_3708_ = leanh::lean_box(0);
                    v_isShared_3709_ = v_isSharedCheck_3742_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_3710_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3698_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3711_ = leanh::lean_ctor_get(v_traceState_3698_, 0);
                v_isSharedCheck_3741_ =
                    (!leanh::lean_is_exclusive(v_traceState_3698_)) as u8;
                if v_isSharedCheck_3741_ == 0 {
                    v___x_3713_ = v_traceState_3698_;
                    v_isShared_3714_ = v_isSharedCheck_3741_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3711_);
                    leanh::lean_dec(v_traceState_3698_);
                    v___x_3713_ = leanh::lean_box(0);
                    v_isShared_3714_ = v_isSharedCheck_3741_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3715_ = (leanh::lean_unbox(v_a_3687_) as u8);
                leanh::lean_dec(v_a_3687_);
                v___x_3716_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3692_, v___x_3715_);
                leanh::lean_dec_ref(v_lctx_3692_);
                leanh::lean_inc_ref(v_options_3682_);
                v___x_3717_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3717_, 0, v_env_3691_);
                leanh::lean_ctor_set(v___x_3717_, 1, v___x_3696_);
                leanh::lean_ctor_set(v___x_3717_, 2, v___x_3716_);
                leanh::lean_ctor_set(v___x_3717_, 3, v_options_3682_);
                if v_isShared_3695_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3694_, 3);
                    leanh::lean_ctor_set(v___x_3694_, 1, v_msg_3676_);
                    leanh::lean_ctor_set(v___x_3694_, 0, v___x_3717_);
                    v___x_3719_ = v___x_3694_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3740_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3717_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_msg_3676_);
                    v___x_3719_ = v_reuseFailAlloc_3740_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3720_ = leanh::lean_box(0);
                v___x_3721_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__3);
                v___x_3722_ = 0;
                v___x_3723_ =
                    l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__4;
                v___x_3724_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_3724_, 0, v_cls_3675_);
                leanh::lean_ctor_set(v___x_3724_, 1, v___x_3720_);
                leanh::lean_ctor_set(v___x_3724_, 2, v___x_3723_);
                leanh::lean_ctor_set_float(
                    v___x_3724_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3721_,
                );
                leanh::lean_ctor_set_float(
                    v___x_3724_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3721_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3724_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3722_,
                );
                v___x_3725_ =
                    l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2___closed__5;
                v___x_3726_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3726_, 0, v___x_3724_);
                leanh::lean_ctor_set(v___x_3726_, 1, v___x_3719_);
                leanh::lean_ctor_set(v___x_3726_, 2, v___x_3725_);
                leanh::lean_inc(v_ref_3683_);
                v___x_3727_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3727_, 0, v_ref_3683_);
                leanh::lean_ctor_set(v___x_3727_, 1, v___x_3726_);
                v___x_3728_ = l_Lean_PersistentArray_push___redArg(v_traces_3711_, v___x_3727_);
                if v_isShared_3714_ == 0 {
                    leanh::lean_ctor_set(v___x_3713_, 0, v___x_3728_);
                    v___x_3730_ = v___x_3713_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3739_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3728_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3739_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3710_,
                    );
                    v___x_3730_ = v_reuseFailAlloc_3739_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3709_ == 0 {
                    leanh::lean_ctor_set(v___x_3708_, 4, v___x_3730_);
                    v___x_3732_ = v___x_3708_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3738_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_env_3699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_nextMacroScope_3700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 2, v_ngen_3701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 3, v_auxDeclNGen_3702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 4, v___x_3730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 5, v_cache_3703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 6, v_messages_3704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 7, v_infoState_3705_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 8, v_snapshotTasks_3706_);
                    v___x_3732_ = v_reuseFailAlloc_3738_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3733_ = lean_st_ref_set(v___y_3680_, v___x_3732_);
                v___x_3734_ = leanh::lean_box(0);
                if v_isShared_3690_ == 0 {
                    leanh::lean_ctor_set(v___x_3689_, 0, v___x_3734_);
                    v___x_3736_ = v___x_3689_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
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
                    v_reuseFailAlloc_3752_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
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
    mut v_cls_3754_: *mut leanh::LeanObject,
    mut v_msg_3755_: *mut leanh::LeanObject,
    mut v___y_3756_: *mut leanh::LeanObject,
    mut v___y_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3761_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(
        v_cls_3754_,
        v_msg_3755_,
        v___y_3756_,
        v___y_3757_,
        v___y_3758_,
        v___y_3759_,
    );
    leanh::lean_dec(v___y_3759_);
    leanh::lean_dec_ref(v___y_3758_);
    leanh::lean_dec(v___y_3757_);
    leanh::lean_dec_ref(v___y_3756_);
    return v_res_3761_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(
    mut v_xs_3762_: *mut leanh::LeanObject,
    mut v_ys_3763_: *mut leanh::LeanObject,
    mut v_x_3764_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3766_: u8 = 0;
    let mut v_one_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3765_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3766_ = lean_nat_dec_eq(v_x_3764_, v_zero_3765_);
                if v_isZero_3766_ == 1 {
                    leanh::lean_dec(v_x_3764_);
                    return v_isZero_3766_;
                } else {
                    v_one_3767_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3768_ = lean_nat_sub(v_x_3764_, v_one_3767_);
                    leanh::lean_dec(v_x_3764_);
                    v___x_3769_ = lean_array_fget_borrowed(v_xs_3762_, v_n_3768_);
                    v___x_3770_ = lean_array_fget_borrowed(v_ys_3763_, v_n_3768_);
                    v___x_3771_ = lean_nat_dec_eq(v___x_3769_, v___x_3770_);
                    if v___x_3771_ == 0 {
                        leanh::lean_dec(v_n_3768_);
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
    mut v_xs_3773_: *mut leanh::LeanObject,
    mut v_ys_3774_: *mut leanh::LeanObject,
    mut v_x_3775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3776_: u8 = 0;
    let mut v_r_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3776_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_3773_, v_ys_3774_, v_x_3775_);
    leanh::lean_dec_ref(v_ys_3774_);
    leanh::lean_dec_ref(v_xs_3773_);
    v_r_3777_ = leanh::lean_box((v_res_3776_) as usize);
    return v_r_3777_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(
    mut v_x_3778_: *mut leanh::LeanObject,
    mut v_x_3779_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3778_) == 0 {
        if leanh::lean_obj_tag(v_x_3779_) == 0 {
            let mut v___x_3780_: u8 = 0;
            v___x_3780_ = 1;
            return v___x_3780_;
        } else {
            let mut v___x_3781_: u8 = 0;
            v___x_3781_ = 0;
            return v___x_3781_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_3779_) == 0 {
            let mut v___x_3782_: u8 = 0;
            v___x_3782_ = 0;
            return v___x_3782_;
        } else {
            let mut v_val_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3787_: u8 = 0;
            v_val_3783_ = leanh::lean_ctor_get(v_x_3778_, 0);
            v_val_3784_ = leanh::lean_ctor_get(v_x_3779_, 0);
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
    mut v_x_3789_: *mut leanh::LeanObject,
    mut v_x_3790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3791_: u8 = 0;
    let mut v_r_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(
        v_x_3789_, v_x_3790_,
    );
    leanh::lean_dec(v_x_3790_);
    leanh::lean_dec(v_x_3789_);
    v_r_3792_ = leanh::lean_box((v_res_3791_) as usize);
    return v_r_3792_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(
    mut v_x_3795_: *mut leanh::LeanObject,
    mut v_specArgs_x3f_3796_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: u8 = 0;
    v___x_3797_ = l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___closed__0;
    v___x_3798_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0(
        v_specArgs_x3f_3796_,
        v___x_3797_,
    );
    return v___x_3798_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveSpecEntries___lam__0___boxed(
    mut v_x_3799_: *mut leanh::LeanObject,
    mut v_specArgs_x3f_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3801_: u8 = 0;
    let mut v_r_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3801_ = l_Lean_Compiler_LCNF_saveSpecEntries___lam__0(v_x_3799_, v_specArgs_x3f_3800_);
    leanh::lean_dec(v_specArgs_x3f_3800_);
    leanh::lean_dec(v_x_3799_);
    v_r_3802_ = leanh::lean_box((v_res_3801_) as usize);
    return v_r_3802_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(
    mut v_a_3803_: *mut leanh::LeanObject,
    mut v_a_3804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___y_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weak_3817_: u8 = 0;
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3803_) == 0 {
                    v___x_3805_ = l_List_reverse___redArg(v_a_3804_);
                    return v___x_3805_;
                } else {
                    v_head_3806_ = leanh::lean_ctor_get(v_a_3803_, 0);
                    v_tail_3807_ = leanh::lean_ctor_get(v_a_3803_, 1);
                    v_isSharedCheck_3824_ = (!leanh::lean_is_exclusive(v_a_3803_)) as u8;
                    if v_isSharedCheck_3824_ == 0 {
                        v___x_3809_ = v_a_3803_;
                        v_isShared_3810_ = v_isSharedCheck_3824_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3807_);
                        leanh::lean_inc(v_head_3806_);
                        leanh::lean_dec(v_a_3803_);
                        v___x_3809_ = leanh::lean_box(0);
                        v_isShared_3810_ = v_isSharedCheck_3824_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_head_3806_) {
                0 => {
                    v_weak_3817_ = leanh::lean_ctor_get_uint8(v_head_3806_, 0 as u32);
                    leanh::lean_dec_ref_known(v_head_3806_, 0);
                    if v_weak_3817_ == 0 {
                        v___x_3818_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__2);
                        v___y_3812_ = v___x_3818_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3819_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__5);
                        v___y_3812_ = v___x_3819_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v___x_3820_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__8);
                    v___y_3812_ = v___x_3820_;
                    state = 2;
                    continue;
                }
                2 => {
                    v___x_3821_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__11);
                    v___y_3812_ = v___x_3821_;
                    state = 2;
                    continue;
                }
                3 => {
                    v___x_3822_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__14);
                    v___y_3812_ = v___x_3822_;
                    state = 2;
                    continue;
                }
                _ => {
                    v___x_3823_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17_once), _init_l_Lean_Compiler_LCNF_instToMessageDataSpecParamInfo___lam__0___closed__17);
                    v___y_3812_ = v___x_3823_;
                    state = 2;
                    continue;
                }
            },
            2 => {
                leanh::lean_inc_ref(v___y_3812_);
                if v_isShared_3810_ == 0 {
                    leanh::lean_ctor_set(v___x_3809_, 1, v_a_3804_);
                    leanh::lean_ctor_set(v___x_3809_, 0, v___y_3812_);
                    v___x_3814_ = v___x_3809_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___y_3812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_a_3804_);
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
-> *mut leanh::LeanObject {
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3825_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3826_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__0);
    v___x_3827_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3827_, 0, v___x_3826_);
    return v___x_3827_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__1);
    v___x_3829_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3829_, 0, v___x_3828_);
    leanh::lean_ctor_set(v___x_3829_, 1, v___x_3828_);
    return v___x_3829_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5;
    v___x_3840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__7;
    v___x_3841_ = l_Lean_Name_append(v___x_3840_, v___x_3839_);
    return v___x_3841_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__9;
    v___x_3844_ = l_Lean_stringToMessageData(v___x_3843_);
    return v___x_3844_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(
    mut v_as_3845_: *mut leanh::LeanObject,
    mut v_sz_3846_: usize,
    mut v_i_3847_: usize,
    mut v_b_3848_: *mut leanh::LeanObject,
    mut v___y_3849_: *mut leanh::LeanObject,
    mut v___y_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: usize = 0;
    let mut v___x_3857_: usize = 0;
    let mut v___x_3859_: u8 = 0;
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsInfo_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3889_: u8 = 0;
    let mut v_unused_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: u8 = 0;
    let mut v___x_3894_: usize = 0;
    let mut v___x_3895_: usize = 0;
    let mut v___x_3896_: u8 = 0;
    let mut v_options_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3898_: u8 = 0;
    let mut v_inheritedTraceOptions_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3859_ = lean_usize_dec_lt(v_i_3847_, v_sz_3846_);
                if v___x_3859_ == 0 {
                    v___x_3860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3860_, 0, v_b_3848_);
                    return v___x_3860_;
                } else {
                    v_a_3861_ = lean_array_uget_borrowed(v_as_3845_, v_i_3847_);
                    v_declName_3862_ = leanh::lean_ctor_get(v_a_3861_, 0);
                    v_paramsInfo_3863_ = leanh::lean_ctor_get(v_a_3861_, 1);
                    v___x_3864_ = leanh::lean_box(0);
                    v___x_3891_ = leanh::lean_unsigned_to_nat(0);
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
                                v_options_3897_ = leanh::lean_ctor_get(v___y_3851_, 2);
                                v_hasTrace_3898_ = leanh::lean_ctor_get_uint8(
                                    v_options_3897_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                        as u32,
                                );
                                if v_hasTrace_3898_ == 0 {
                                    v___y_3866_ = v___y_3852_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_inheritedTraceOptions_3899_ =
                                        leanh::lean_ctor_get(v___y_3851_, 13);
                                    v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5;
                                    v___x_3901_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__8);
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
                                        leanh::lean_inc(v_declName_3862_);
                                        v___x_3903_ = l_Lean_MessageData_ofName(v_declName_3862_);
                                        v___x_3904_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__10);
                                        v___x_3905_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3905_, 0, v___x_3903_);
                                        leanh::lean_ctor_set(v___x_3905_, 1, v___x_3904_);
                                        leanh::lean_inc_ref(v_paramsInfo_3863_);
                                        v___x_3906_ = lean_array_to_list(v_paramsInfo_3863_);
                                        v___x_3907_ = leanh::lean_box(0);
                                        v___x_3908_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__1(v___x_3906_, v___x_3907_);
                                        v___x_3909_ = l_Lean_MessageData_ofList(v___x_3908_);
                                        v___x_3910_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3910_, 0, v___x_3905_);
                                        leanh::lean_ctor_set(v___x_3910_, 1, v___x_3909_);
                                        v___x_3911_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__2(v___x_3900_, v___x_3910_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
                                        if leanh::lean_obj_tag(v___x_3911_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_3911_, 1);
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
                v_env_3868_ = leanh::lean_ctor_get(v___x_3867_, 0);
                v_nextMacroScope_3869_ = leanh::lean_ctor_get(v___x_3867_, 1);
                v_ngen_3870_ = leanh::lean_ctor_get(v___x_3867_, 2);
                v_auxDeclNGen_3871_ = leanh::lean_ctor_get(v___x_3867_, 3);
                v_traceState_3872_ = leanh::lean_ctor_get(v___x_3867_, 4);
                v_messages_3873_ = leanh::lean_ctor_get(v___x_3867_, 6);
                v_infoState_3874_ = leanh::lean_ctor_get(v___x_3867_, 7);
                v_snapshotTasks_3875_ = leanh::lean_ctor_get(v___x_3867_, 8);
                v_isSharedCheck_3889_ = (!leanh::lean_is_exclusive(v___x_3867_)) as u8;
                if v_isSharedCheck_3889_ == 0 {
                    v_unused_3890_ = leanh::lean_ctor_get(v___x_3867_, 5);
                    leanh::lean_dec(v_unused_3890_);
                    v___x_3877_ = v___x_3867_;
                    v_isShared_3878_ = v_isSharedCheck_3889_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3875_);
                    leanh::lean_inc(v_infoState_3874_);
                    leanh::lean_inc(v_messages_3873_);
                    leanh::lean_inc(v_traceState_3872_);
                    leanh::lean_inc(v_auxDeclNGen_3871_);
                    leanh::lean_inc(v_ngen_3870_);
                    leanh::lean_inc(v_nextMacroScope_3869_);
                    leanh::lean_inc(v_env_3868_);
                    leanh::lean_dec(v___x_3867_);
                    v___x_3877_ = leanh::lean_box(0);
                    v_isShared_3878_ = v_isSharedCheck_3889_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3879_ = l_Lean_Compiler_LCNF_specExtension;
                v_toEnvExtension_3880_ = leanh::lean_ctor_get(v___x_3879_, 0);
                v_asyncMode_3881_ = leanh::lean_ctor_get(v_toEnvExtension_3880_, 2);
                v___x_3882_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_3861_);
                v___x_3883_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3879_,
                    v_env_3868_,
                    v_a_3861_,
                    v_asyncMode_3881_,
                    v___x_3882_,
                );
                v___x_3884_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__2);
                if v_isShared_3878_ == 0 {
                    leanh::lean_ctor_set(v___x_3877_, 5, v___x_3884_);
                    leanh::lean_ctor_set(v___x_3877_, 0, v___x_3883_);
                    v___x_3886_ = v___x_3877_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3883_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_nextMacroScope_3869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 2, v_ngen_3870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 3, v_auxDeclNGen_3871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 4, v_traceState_3872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 5, v___x_3884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 6, v_messages_3873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 7, v_infoState_3874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 8, v_snapshotTasks_3875_);
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
    mut v_as_3912_: *mut leanh::LeanObject,
    mut v_sz_3913_: *mut leanh::LeanObject,
    mut v_i_3914_: *mut leanh::LeanObject,
    mut v_b_3915_: *mut leanh::LeanObject,
    mut v___y_3916_: *mut leanh::LeanObject,
    mut v___y_3917_: *mut leanh::LeanObject,
    mut v___y_3918_: *mut leanh::LeanObject,
    mut v___y_3919_: *mut leanh::LeanObject,
    mut v___y_3920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3921_: usize = 0;
    let mut v_i_boxed_3922_: usize = 0;
    let mut v_res_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3921_ = leanh::lean_unbox_usize(v_sz_3913_);
    leanh::lean_dec(v_sz_3913_);
    v_i_boxed_3922_ = leanh::lean_unbox_usize(v_i_3914_);
    leanh::lean_dec(v_i_3914_);
    v_res_3923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_as_3912_, v_sz_boxed_3921_, v_i_boxed_3922_, v_b_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
    leanh::lean_dec(v___y_3919_);
    leanh::lean_dec_ref(v___y_3918_);
    leanh::lean_dec(v___y_3917_);
    leanh::lean_dec_ref(v___y_3916_);
    leanh::lean_dec_ref(v_as_3912_);
    return v_res_3923_;
}
pub unsafe fn l_Lean_Compiler_LCNF_saveSpecEntries(
    mut v_decls_3925_: *mut leanh::LeanObject,
    mut v_a_3926_: *mut leanh::LeanObject,
    mut v_a_3927_: *mut leanh::LeanObject,
    mut v_a_3928_: *mut leanh::LeanObject,
    mut v_a_3929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3939_: usize = 0;
    let mut v___x_3940_: usize = 0;
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3944_: u8 = 0;
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3948_: u8 = 0;
    let mut v_unused_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3953_: u8 = 0;
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3931_ = l_Lean_Compiler_LCNF_saveSpecEntries___closed__0;
                v___x_3932_ = lean_array_get_size(v_decls_3925_);
                v___x_3933_ = 0;
                v___x_3934_ = leanh::lean_box((v___x_3933_) as usize);
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
                leanh::lean_dec_ref(v___x_3935_);
                if leanh::lean_obj_tag(v___x_3936_) == 0 {
                    v_a_3937_ = leanh::lean_ctor_get(v___x_3936_, 0);
                    leanh::lean_inc(v_a_3937_);
                    leanh::lean_dec_ref_known(v___x_3936_, 1);
                    v___x_3938_ = leanh::lean_box(0);
                    v_sz_3939_ = lean_array_size(v_a_3937_);
                    v___x_3940_ = 0usize;
                    v___x_3941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3(v_a_3937_, v_sz_3939_, v___x_3940_, v___x_3938_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
                    leanh::lean_dec(v_a_3937_);
                    if leanh::lean_obj_tag(v___x_3941_) == 0 {
                        v_isSharedCheck_3948_ =
                            (!leanh::lean_is_exclusive(v___x_3941_)) as u8;
                        if v_isSharedCheck_3948_ == 0 {
                            v_unused_3949_ = leanh::lean_ctor_get(v___x_3941_, 0);
                            leanh::lean_dec(v_unused_3949_);
                            v___x_3943_ = v___x_3941_;
                            v_isShared_3944_ = v_isSharedCheck_3948_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3941_);
                            v___x_3943_ = leanh::lean_box(0);
                            v_isShared_3944_ = v_isSharedCheck_3948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3941_;
                    }
                } else {
                    v_a_3950_ = leanh::lean_ctor_get(v___x_3936_, 0);
                    v_isSharedCheck_3957_ = (!leanh::lean_is_exclusive(v___x_3936_)) as u8;
                    if v_isSharedCheck_3957_ == 0 {
                        v___x_3952_ = v___x_3936_;
                        v_isShared_3953_ = v_isSharedCheck_3957_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3950_);
                        leanh::lean_dec(v___x_3936_);
                        v___x_3952_ = leanh::lean_box(0);
                        v_isShared_3953_ = v_isSharedCheck_3957_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3944_ == 0 {
                    leanh::lean_ctor_set(v___x_3943_, 0, v___x_3938_);
                    v___x_3946_ = v___x_3943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3947_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3938_);
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
                    v_reuseFailAlloc_3956_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
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
    mut v_decls_3958_: *mut leanh::LeanObject,
    mut v_a_3959_: *mut leanh::LeanObject,
    mut v_a_3960_: *mut leanh::LeanObject,
    mut v_a_3961_: *mut leanh::LeanObject,
    mut v_a_3962_: *mut leanh::LeanObject,
    mut v_a_3963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3964_ = l_Lean_Compiler_LCNF_saveSpecEntries(
        v_decls_3958_,
        v_a_3959_,
        v_a_3960_,
        v_a_3961_,
        v_a_3962_,
    );
    leanh::lean_dec(v_a_3962_);
    leanh::lean_dec_ref(v_a_3961_);
    leanh::lean_dec(v_a_3960_);
    leanh::lean_dec_ref(v_a_3959_);
    return v_res_3964_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(
    mut v_xs_3965_: *mut leanh::LeanObject,
    mut v_ys_3966_: *mut leanh::LeanObject,
    mut v_hsz_3967_: *mut leanh::LeanObject,
    mut v_x_3968_: *mut leanh::LeanObject,
    mut v_x_3969_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3970_: u8 = 0;
    v___x_3970_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___redArg(v_xs_3965_, v_ys_3966_, v_x_3968_);
    return v___x_3970_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0___boxed(
    mut v_xs_3971_: *mut leanh::LeanObject,
    mut v_ys_3972_: *mut leanh::LeanObject,
    mut v_hsz_3973_: *mut leanh::LeanObject,
    mut v_x_3974_: *mut leanh::LeanObject,
    mut v_x_3975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3976_: u8 = 0;
    let mut v_r_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3976_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__0_spec__0(v_xs_3971_, v_ys_3972_, v_hsz_3973_, v_x_3974_, v_x_3975_);
    leanh::lean_dec_ref(v_ys_3972_);
    leanh::lean_dec_ref(v_xs_3971_);
    v_r_3977_ = leanh::lean_box((v_res_3976_) as usize);
    return v_r_3977_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(
    mut v_as_3978_: *mut leanh::LeanObject,
    mut v_k_3979_: *mut leanh::LeanObject,
    mut v_x_3980_: *mut leanh::LeanObject,
    mut v_x_3981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: u8 = 0;
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: u8 = 0;
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: u8 = 0;
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3982_ = lean_nat_add(v_x_3980_, v_x_3981_);
                v___x_3983_ = leanh::lean_unsigned_to_nat(1);
                v_m_3984_ = lean_nat_shiftr(v___x_3982_, v___x_3983_);
                leanh::lean_dec(v___x_3982_);
                v_a_3985_ = lean_array_fget_borrowed(v_as_3978_, v_m_3984_);
                v___x_3986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_a_3985_, v_k_3979_);
                if v___x_3986_ == 0 {
                    leanh::lean_dec(v_x_3981_);
                    v___x_3987_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2__spec__0___redArg___lam__0(v_k_3979_, v_a_3985_);
                    if v___x_3987_ == 0 {
                        leanh::lean_dec(v_m_3984_);
                        leanh::lean_dec(v_x_3980_);
                        leanh::lean_inc(v_a_3985_);
                        v___x_3988_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3988_, 0, v_a_3985_);
                        return v___x_3988_;
                    } else {
                        v___x_3989_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3990_ = lean_nat_dec_eq(v_m_3984_, v___x_3989_);
                        if v___x_3990_ == 0 {
                            v___x_3991_ = lean_nat_sub(v_m_3984_, v___x_3983_);
                            leanh::lean_dec(v_m_3984_);
                            v___x_3992_ = lean_nat_dec_lt(v___x_3991_, v_x_3980_);
                            if v___x_3992_ == 0 {
                                v_x_3981_ = v___x_3991_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3991_);
                                leanh::lean_dec(v_x_3980_);
                                v___x_3994_ = leanh::lean_box(0);
                                return v___x_3994_;
                            }
                        } else {
                            leanh::lean_dec(v_m_3984_);
                            leanh::lean_dec(v_x_3980_);
                            v___x_3995_ = leanh::lean_box(0);
                            return v___x_3995_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_x_3980_);
                    v___x_3996_ = lean_nat_add(v_m_3984_, v___x_3983_);
                    leanh::lean_dec(v_m_3984_);
                    v___x_3997_ = lean_nat_dec_le(v___x_3996_, v_x_3981_);
                    if v___x_3997_ == 0 {
                        leanh::lean_dec(v___x_3996_);
                        leanh::lean_dec(v_x_3981_);
                        v___x_3998_ = leanh::lean_box(0);
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
    mut v_as_4000_: *mut leanh::LeanObject,
    mut v_k_4001_: *mut leanh::LeanObject,
    mut v_x_4002_: *mut leanh::LeanObject,
    mut v_x_4003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4004_ =
        l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(
            v_as_4000_, v_k_4001_, v_x_4002_, v_x_4003_,
        );
    leanh::lean_dec_ref(v_k_4001_);
    leanh::lean_dec_ref(v_as_4000_);
    return v_res_4004_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4005_: *mut leanh::LeanObject,
    mut v_vals_4006_: *mut leanh::LeanObject,
    mut v_i_4007_: *mut leanh::LeanObject,
    mut v_k_4008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: u8 = 0;
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4009_ = lean_array_get_size(v_keys_4005_);
                v___x_4010_ = lean_nat_dec_lt(v_i_4007_, v___x_4009_);
                if v___x_4010_ == 0 {
                    leanh::lean_dec(v_i_4007_);
                    v___x_4011_ = leanh::lean_box(0);
                    return v___x_4011_;
                } else {
                    v_k_x27_4012_ = lean_array_fget_borrowed(v_keys_4005_, v_i_4007_);
                    v___x_4013_ = lean_name_eq(v_k_4008_, v_k_x27_4012_);
                    if v___x_4013_ == 0 {
                        v___x_4014_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4015_ = lean_nat_add(v_i_4007_, v___x_4014_);
                        leanh::lean_dec(v_i_4007_);
                        v_i_4007_ = v___x_4015_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4017_ = lean_array_fget_borrowed(v_vals_4006_, v_i_4007_);
                        leanh::lean_dec(v_i_4007_);
                        leanh::lean_inc(v___x_4017_);
                        v___x_4018_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4018_, 0, v___x_4017_);
                        return v___x_4018_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4019_: *mut leanh::LeanObject,
    mut v_vals_4020_: *mut leanh::LeanObject,
    mut v_i_4021_: *mut leanh::LeanObject,
    mut v_k_4022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4019_, v_vals_4020_, v_i_4021_, v_k_4022_);
    leanh::lean_dec(v_k_4022_);
    leanh::lean_dec_ref(v_vals_4020_);
    leanh::lean_dec_ref(v_keys_4019_);
    return v_res_4023_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(
    mut v_x_4024_: *mut leanh::LeanObject,
    mut v_x_4025_: usize,
    mut v_x_4026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: usize = 0;
    let mut v___x_4030_: usize = 0;
    let mut v___x_4031_: usize = 0;
    let mut v_j_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: u8 = 0;
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: usize = 0;
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4024_) == 0 {
                    v_es_4027_ = leanh::lean_ctor_get(v_x_4024_, 0);
                    v___x_4028_ = leanh::lean_box(2);
                    v___x_4029_ = 5usize;
                    v___x_4030_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0___redArg___closed__1);
                    v___x_4031_ = lean_usize_land(v_x_4025_, v___x_4030_);
                    v_j_4032_ = lean_usize_to_nat(v___x_4031_);
                    v___x_4033_ = lean_array_get_borrowed(v___x_4028_, v_es_4027_, v_j_4032_);
                    leanh::lean_dec(v_j_4032_);
                    match leanh::lean_obj_tag(v___x_4033_) {
                        0 => {
                            v_key_4034_ = leanh::lean_ctor_get(v___x_4033_, 0);
                            v_val_4035_ = leanh::lean_ctor_get(v___x_4033_, 1);
                            v___x_4036_ = lean_name_eq(v_x_4026_, v_key_4034_);
                            if v___x_4036_ == 0 {
                                v___x_4037_ = leanh::lean_box(0);
                                return v___x_4037_;
                            } else {
                                leanh::lean_inc(v_val_4035_);
                                v___x_4038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4038_, 0, v_val_4035_);
                                return v___x_4038_;
                            }
                        }
                        1 => {
                            v_node_4039_ = leanh::lean_ctor_get(v___x_4033_, 0);
                            v___x_4040_ = lean_usize_shift_right(v_x_4025_, v___x_4029_);
                            v_x_4024_ = v_node_4039_;
                            v_x_4025_ = v___x_4040_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4042_ = leanh::lean_box(0);
                            return v___x_4042_;
                        }
                    }
                } else {
                    v_ks_4043_ = leanh::lean_ctor_get(v_x_4024_, 0);
                    v_vs_4044_ = leanh::lean_ctor_get(v_x_4024_, 1);
                    v___x_4045_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4046_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4043_, v_vs_4044_, v___x_4045_, v_x_4026_);
                    return v___x_4046_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4047_: *mut leanh::LeanObject,
    mut v_x_4048_: *mut leanh::LeanObject,
    mut v_x_4049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_413__boxed_4050_: usize = 0;
    let mut v_res_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_413__boxed_4050_ = leanh::lean_unbox_usize(v_x_4048_);
    leanh::lean_dec(v_x_4048_);
    v_res_4051_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_4047_, v_x_413__boxed_4050_, v_x_4049_);
    leanh::lean_dec(v_x_4049_);
    leanh::lean_dec_ref(v_x_4047_);
    return v_res_4051_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(
    mut v_x_4052_: *mut leanh::LeanObject,
    mut v_x_4053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4055_: u64 = 0;
    let mut v___x_4056_: usize = 0;
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: u64 = 0;
    let mut v_hash_4059_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4053_) == 0 {
                    v___x_4058_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_SpecState_addEntry_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4055_ = v___x_4058_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4059_ = leanh::lean_ctor_get_uint64(
                        v_x_4053_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_x_4060_: *mut leanh::LeanObject,
    mut v_x_4061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4062_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_4060_, v_x_4061_);
    leanh::lean_dec(v_x_4061_);
    leanh::lean_dec_ref(v_x_4060_);
    return v_res_4062_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_Compiler_LCNF_instInhabitedSpecState_default;
    v___x_4064_ = leanh::lean_box(0);
    v___x_4065_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4065_, 0, v___x_4064_);
    leanh::lean_ctor_set(v___x_4065_, 1, v___x_4063_);
    return v___x_4065_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(
    mut v_env_4066_: *mut leanh::LeanObject,
    mut v_declName_4067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: u8 = 0;
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4068_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0_once
                    ),
                    _init_l_Lean_Compiler_LCNF_getSpecEntryCore_x3f___closed__0,
                );
                v___x_4069_ = l_Lean_Compiler_LCNF_specExtension;
                v___x_4077_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4066_, v_declName_4067_);
                if leanh::lean_obj_tag(v___x_4077_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_4078_ = leanh::lean_ctor_get(v___x_4077_, 0);
                    leanh::lean_inc(v_val_4078_);
                    leanh::lean_dec_ref_known(v___x_4077_, 1);
                    v___x_4092_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(leanh::lean_box(0), leanh::lean_box(0), leanh::lean_box(0), v___x_4068_, v___x_4069_, v_env_4066_, v_val_4078_);
                    v___x_4093_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4094_ = lean_array_get_size(v___x_4092_);
                    v___x_4095_ = lean_nat_dec_lt(v___x_4093_, v___x_4094_);
                    if v___x_4095_ == 0 {
                        leanh::lean_dec_ref(v___x_4092_);
                        state = 2;
                        continue;
                    } else {
                        v___x_4096_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4097_ = lean_nat_sub(v___x_4094_, v___x_4096_);
                        v___x_4098_ = lean_nat_dec_le(v___x_4093_, v___x_4097_);
                        if v___x_4098_ == 0 {
                            leanh::lean_dec(v___x_4097_);
                            leanh::lean_dec_ref(v___x_4092_);
                            state = 2;
                            continue;
                        } else {
                            v___x_4099_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
                            v___x_4100_ = 0;
                            leanh::lean_inc(v_declName_4067_);
                            v___x_4101_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            leanh::lean_ctor_set(v___x_4101_, 0, v_declName_4067_);
                            leanh::lean_ctor_set(v___x_4101_, 1, v___x_4099_);
                            leanh::lean_ctor_set_uint8(
                                v___x_4101_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                                v___x_4100_,
                            );
                            v___x_4102_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_4092_, v___x_4101_, v___x_4093_, v___x_4097_);
                            leanh::lean_dec_ref_known(v___x_4101_, 2);
                            leanh::lean_dec_ref(v___x_4092_);
                            if leanh::lean_obj_tag(v___x_4102_) == 0 {
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_4078_);
                                leanh::lean_dec(v_declName_4067_);
                                leanh::lean_dec_ref(v_env_4066_);
                                return v___x_4102_;
                            }
                        }
                    }
                }
            }
            1 => {
                v_toEnvExtension_4071_ = leanh::lean_ctor_get(v___x_4069_, 0);
                v_asyncMode_4072_ = leanh::lean_ctor_get(v_toEnvExtension_4071_, 2);
                v___x_4073_ = leanh::lean_box(0);
                v___x_4074_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_4068_,
                    v___x_4069_,
                    v_env_4066_,
                    v_asyncMode_4072_,
                    v___x_4073_,
                );
                v_snd_4075_ = leanh::lean_ctor_get(v___x_4074_, 1);
                leanh::lean_inc(v_snd_4075_);
                leanh::lean_dec(v___x_4074_);
                v___x_4076_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_snd_4075_, v_declName_4067_);
                leanh::lean_dec(v_declName_4067_);
                leanh::lean_dec(v_snd_4075_);
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
                leanh::lean_dec(v_val_4078_);
                v___x_4082_ = leanh::lean_unsigned_to_nat(0);
                v___x_4083_ = lean_array_get_size(v___x_4081_);
                v___x_4084_ = lean_nat_dec_lt(v___x_4082_, v___x_4083_);
                if v___x_4084_ == 0 {
                    leanh::lean_dec_ref(v___x_4081_);
                    state = 1;
                    continue;
                } else {
                    v___x_4085_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4086_ = lean_nat_sub(v___x_4083_, v___x_4085_);
                    v___x_4087_ = lean_nat_dec_le(v___x_4082_, v___x_4086_);
                    if v___x_4087_ == 0 {
                        leanh::lean_dec(v___x_4086_);
                        leanh::lean_dec_ref(v___x_4081_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4088_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_findAtSorted_x3f___closed__0;
                        v___x_4089_ = 0;
                        leanh::lean_inc(v_declName_4067_);
                        v___x_4090_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        leanh::lean_ctor_set(v___x_4090_, 0, v_declName_4067_);
                        leanh::lean_ctor_set(v___x_4090_, 1, v___x_4088_);
                        leanh::lean_ctor_set_uint8(
                            v___x_4090_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v___x_4089_,
                        );
                        v___x_4091_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(v___x_4081_, v___x_4090_, v___x_4082_, v___x_4086_);
                        leanh::lean_dec_ref_known(v___x_4090_, 2);
                        leanh::lean_dec_ref(v___x_4081_);
                        if leanh::lean_obj_tag(v___x_4091_) == 0 {
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_declName_4067_);
                            leanh::lean_dec_ref(v_env_4066_);
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
    mut v_00_u03b2_4103_: *mut leanh::LeanObject,
    mut v_x_4104_: *mut leanh::LeanObject,
    mut v_x_4105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4106_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___redArg(v_x_4104_, v_x_4105_);
    return v___x_4106_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0___boxed(
    mut v_00_u03b2_4107_: *mut leanh::LeanObject,
    mut v_x_4108_: *mut leanh::LeanObject,
    mut v_x_4109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4110_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0(
            v_00_u03b2_4107_,
            v_x_4108_,
            v_x_4109_,
        );
    leanh::lean_dec(v_x_4109_);
    leanh::lean_dec_ref(v_x_4108_);
    return v_res_4110_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(
    mut v_as_4111_: *mut leanh::LeanObject,
    mut v_k_4112_: *mut leanh::LeanObject,
    mut v_x_4113_: *mut leanh::LeanObject,
    mut v_x_4114_: *mut leanh::LeanObject,
    mut v_x_4115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4116_ =
        l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___redArg(
            v_as_4111_, v_k_4112_, v_x_4113_, v_x_4114_,
        );
    return v___x_4116_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1___boxed(
    mut v_as_4117_: *mut leanh::LeanObject,
    mut v_k_4118_: *mut leanh::LeanObject,
    mut v_x_4119_: *mut leanh::LeanObject,
    mut v_x_4120_: *mut leanh::LeanObject,
    mut v_x_4121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4122_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__1(
        v_as_4117_, v_k_4118_, v_x_4119_, v_x_4120_, v_x_4121_,
    );
    leanh::lean_dec_ref(v_k_4118_);
    leanh::lean_dec_ref(v_as_4117_);
    return v_res_4122_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(
    mut v_00_u03b2_4123_: *mut leanh::LeanObject,
    mut v_x_4124_: *mut leanh::LeanObject,
    mut v_x_4125_: usize,
    mut v_x_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___redArg(v_x_4124_, v_x_4125_, v_x_4126_);
    return v___x_4127_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4128_: *mut leanh::LeanObject,
    mut v_x_4129_: *mut leanh::LeanObject,
    mut v_x_4130_: *mut leanh::LeanObject,
    mut v_x_4131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_579__boxed_4132_: usize = 0;
    let mut v_res_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_579__boxed_4132_ = leanh::lean_unbox_usize(v_x_4130_);
    leanh::lean_dec(v_x_4130_);
    v_res_4133_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0(v_00_u03b2_4128_, v_x_4129_, v_x_579__boxed_4132_, v_x_4131_);
    leanh::lean_dec(v_x_4131_);
    leanh::lean_dec_ref(v_x_4129_);
    return v_res_4133_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4134_: *mut leanh::LeanObject,
    mut v_keys_4135_: *mut leanh::LeanObject,
    mut v_vals_4136_: *mut leanh::LeanObject,
    mut v_heq_4137_: *mut leanh::LeanObject,
    mut v_i_4138_: *mut leanh::LeanObject,
    mut v_k_4139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4135_, v_vals_4136_, v_i_4138_, v_k_4139_);
    return v___x_4140_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4141_: *mut leanh::LeanObject,
    mut v_keys_4142_: *mut leanh::LeanObject,
    mut v_vals_4143_: *mut leanh::LeanObject,
    mut v_heq_4144_: *mut leanh::LeanObject,
    mut v_i_4145_: *mut leanh::LeanObject,
    mut v_k_4146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4147_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getSpecEntryCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4141_, v_keys_4142_, v_vals_4143_, v_heq_4144_, v_i_4145_, v_k_4146_);
    leanh::lean_dec(v_k_4146_);
    leanh::lean_dec_ref(v_vals_4143_);
    leanh::lean_dec_ref(v_keys_4142_);
    return v_res_4147_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0(
    mut v_declName_4148_: *mut leanh::LeanObject,
    mut v_toPure_4149_: *mut leanh::LeanObject,
    mut v_____do__lift_4150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4151_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_4150_, v_declName_4148_);
    v___x_4152_ =
        leanh::lean_apply_2(v_toPure_4149_, leanh::lean_box(0), v___x_4151_);
    return v___x_4152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(
    mut v_inst_4153_: *mut leanh::LeanObject,
    mut v_inst_4154_: *mut leanh::LeanObject,
    mut v_declName_4155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4156_ = leanh::lean_ctor_get(v_inst_4153_, 0);
    leanh::lean_inc_ref(v_toApplicative_4156_);
    v_toBind_4157_ = leanh::lean_ctor_get(v_inst_4153_, 1);
    leanh::lean_inc(v_toBind_4157_);
    leanh::lean_dec_ref(v_inst_4153_);
    v_getEnv_4158_ = leanh::lean_ctor_get(v_inst_4154_, 0);
    leanh::lean_inc(v_getEnv_4158_);
    leanh::lean_dec_ref(v_inst_4154_);
    v_toPure_4159_ = leanh::lean_ctor_get(v_toApplicative_4156_, 1);
    leanh::lean_inc(v_toPure_4159_);
    leanh::lean_dec_ref(v_toApplicative_4156_);
    v___f_4160_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4160_, 0, v_declName_4155_);
    leanh::lean_closure_set(v___f_4160_, 1, v_toPure_4159_);
    v___x_4161_ = leanh::lean_apply_4(
        v_toBind_4157_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4158_,
        v___f_4160_,
    );
    return v___x_4161_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSpecEntry_x3f(
    mut v_m_4162_: *mut leanh::LeanObject,
    mut v_inst_4163_: *mut leanh::LeanObject,
    mut v_inst_4164_: *mut leanh::LeanObject,
    mut v_declName_4165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4166_ = l_Lean_Compiler_LCNF_getSpecEntry_x3f___redArg(
        v_inst_4163_,
        v_inst_4164_,
        v_declName_4165_,
    );
    return v___x_4166_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0(
    mut v_declName_4167_: *mut leanh::LeanObject,
    mut v_toPure_4168_: *mut leanh::LeanObject,
    mut v_____do__lift_4169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4170_ = l_Lean_Compiler_LCNF_getSpecEntryCore_x3f(v_____do__lift_4169_, v_declName_4167_);
    if leanh::lean_obj_tag(v___x_4170_) == 0 {
        let mut v___x_4171_: u8 = 0;
        let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4171_ = 0;
        v___x_4172_ = leanh::lean_box((v___x_4171_) as usize);
        v___x_4173_ =
            leanh::lean_apply_2(v_toPure_4168_, leanh::lean_box(0), v___x_4172_);
        return v___x_4173_;
    } else {
        let mut v___x_4174_: u8 = 0;
        let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_4170_, 1);
        v___x_4174_ = 1;
        v___x_4175_ = leanh::lean_box((v___x_4174_) as usize);
        v___x_4176_ =
            leanh::lean_apply_2(v_toPure_4168_, leanh::lean_box(0), v___x_4175_);
        return v___x_4176_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isSpecCandidate___redArg(
    mut v_inst_4177_: *mut leanh::LeanObject,
    mut v_inst_4178_: *mut leanh::LeanObject,
    mut v_declName_4179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4180_ = leanh::lean_ctor_get(v_inst_4177_, 0);
    leanh::lean_inc_ref(v_toApplicative_4180_);
    v_toBind_4181_ = leanh::lean_ctor_get(v_inst_4177_, 1);
    leanh::lean_inc(v_toBind_4181_);
    leanh::lean_dec_ref(v_inst_4177_);
    v_getEnv_4182_ = leanh::lean_ctor_get(v_inst_4178_, 0);
    leanh::lean_inc(v_getEnv_4182_);
    leanh::lean_dec_ref(v_inst_4178_);
    v_toPure_4183_ = leanh::lean_ctor_get(v_toApplicative_4180_, 1);
    leanh::lean_inc(v_toPure_4183_);
    leanh::lean_dec_ref(v_toApplicative_4180_);
    v___f_4184_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_isSpecCandidate___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4184_, 0, v_declName_4179_);
    leanh::lean_closure_set(v___f_4184_, 1, v_toPure_4183_);
    v___x_4185_ = leanh::lean_apply_4(
        v_toBind_4181_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4182_,
        v___f_4184_,
    );
    return v___x_4185_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isSpecCandidate(
    mut v_m_4186_: *mut leanh::LeanObject,
    mut v_inst_4187_: *mut leanh::LeanObject,
    mut v_inst_4188_: *mut leanh::LeanObject,
    mut v_declName_4189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4190_ =
        l_Lean_Compiler_LCNF_isSpecCandidate___redArg(v_inst_4187_, v_inst_4188_, v_declName_4189_);
    return v___x_4190_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: u8 = 0;
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_saveSpecEntries_spec__3___closed__5;
    v___x_4256_ = 0;
    v___x_4257_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_;
    v___x_4258_ = l_Lean_registerTraceClass(v___x_4255_, v___x_4256_, v___x_4257_);
    return v___x_4258_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2____boxed(
    mut v_a_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4260_ = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
    return v_res_4260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_SpecInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_FixedParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instInhabitedSpecState_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState_default();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedSpecState_default);
    l_Lean_Compiler_LCNF_instInhabitedSpecState =
        _init_l_Lean_Compiler_LCNF_instInhabitedSpecState();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedSpecState);
    res = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_3827028689____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_specExtension = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_specExtension);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_SpecInfo_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SpecInfo_513551779____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_SpecInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_SpecInfo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_FixedParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
}