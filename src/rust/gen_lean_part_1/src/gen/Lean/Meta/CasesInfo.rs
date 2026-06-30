// Lean compiler output
// Module: Lean.Meta.CasesInfo
// Imports: Lean.Meta.Basic Init.Data.Range.Polymorphic.Iterators
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv,
    lean_infer_type, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_mk_ref, lean_st_ref_get,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AuxRecursor::l_Lean_isCasesOnLike;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_contains,
    l_Lean_Environment_findAsync_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_constName_x3f, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getForallBody, l_Lean_Expr_isApp, l_Lean_Expr_isFVar, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
pub static l_instInhabitedCasesAltInfo_default___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
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
static mut l_instInhabitedCasesAltInfo_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instInhabitedCasesAltInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_instInhabitedCasesAltInfo_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instInhabitedCasesAltInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_instInhabitedCasesAltInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instInhabitedCasesAltInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_panic___at___00getCasesInfo_x3f_spec__1___closed__0_value:
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
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00getCasesInfo_x3f_spec__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00getCasesInfo_x3f_spec__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__0_value:
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
    m_data: [96, 0],
};
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__2_value:
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
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
        111, 114, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__4_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0],
};
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__5_value:
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
    m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0],
};
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 97, 115, 101, 115, 73, 110, 102, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [103, 101, 116, 67, 97, 115, 101, 115, 73, 110, 102, 111, 63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__2_value: leanh::LeanStringObject<41> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 109, 114, 46, 105, 115, 65, 112, 112, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__5_value: leanh::LeanStringObject<61> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 109, 111, 116, 105, 118, 101, 65, 114, 103, 32, 61, 61, 32, 120, 115, 91, 100, 105, 115, 99, 114, 80, 111, 115, 93, 33, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_getCasesInfo_x3f___lam__0___closed__0_value: leanh::LeanStringObject<36> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 114, 46, 105, 115, 65, 112, 112, 10, 32, 32, 32, 32, 32, 32, 0,
        ],
    };
static mut l_getCasesInfo_x3f___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_getCasesInfo_x3f___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_getCasesInfo_x3f___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_getCasesInfo_x3f___lam__0___closed__2_value: leanh::LeanStringObject<64> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 64,
        m_capacity: 64,
        m_length: 63,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 114, 46, 97, 112, 112, 65, 114, 103, 33, 46, 105, 115, 70, 86, 97, 114,
            32, 32, 45, 45, 32, 109, 97, 106, 111, 114, 32, 97, 114, 103, 117, 109, 101, 110, 116,
            10, 32, 32, 32, 32, 32, 32, 0,
        ],
    };
static mut l_getCasesInfo_x3f___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_getCasesInfo_x3f___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_getCasesInfo_x3f___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_getCasesInfo_x3f___lam__0___closed__4_value: leanh::LeanStringObject<56> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 56,
        m_capacity: 56,
        m_length: 55,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 114, 46, 103, 101, 116, 65, 112, 112, 70, 110, 46, 105, 115, 70, 86, 97,
            114, 32, 45, 45, 32, 109, 111, 116, 105, 118, 101, 10, 32, 32, 32, 32, 32, 32, 0,
        ],
    };
static mut l_getCasesInfo_x3f___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_getCasesInfo_x3f___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_getCasesInfo_x3f___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_getCasesInfo_x3f___lam__0___closed__6_value: leanh::LeanArrayObject<0> =
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
static mut l_getCasesInfo_x3f___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_getCasesInfo_x3f___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_getCasesInfo_x3f___lam__0___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_getCasesInfo_x3f___lam__0___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_getCasesInfo_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_getCasesInfo_x3f___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_getCasesInfo_x3f___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_getCasesInfo_x3f___closed__3_value: leanh::LeanArrayObject<0> =
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
static mut l_getCasesInfo_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_getCasesInfo_x3f___closed__3_value) as *mut leanh::LeanObject;
static mut l_getCasesInfo_x3f___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_getCasesInfo_x3f___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_getCasesInfo_x3f___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_getCasesInfo_x3f___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_getCasesInfo_x3f___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_CasesAltInfo_ctorIdx(
    mut v_x_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1177_) == 0 {
        let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1178_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1178_;
    } else {
        let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1179_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1179_;
    }
}
pub unsafe fn l_CasesAltInfo_ctorIdx___boxed(
    mut v_x_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_CasesAltInfo_ctorIdx(v_x_1180_);
    leanh::lean_dec_ref(v_x_1180_);
    return v_res_1181_;
}
pub unsafe fn l_CasesAltInfo_ctorElim___redArg(
    mut v_t_1182_: *mut leanh::LeanObject,
    mut v_k_1183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1182_) == 0 {
        let mut v_ctorName_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_numFields_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ctorName_1184_ = leanh::lean_ctor_get(v_t_1182_, 0);
        leanh::lean_inc(v_ctorName_1184_);
        v_numFields_1185_ = leanh::lean_ctor_get(v_t_1182_, 1);
        leanh::lean_inc(v_numFields_1185_);
        leanh::lean_dec_ref_known(v_t_1182_, 2);
        v___x_1186_ = leanh::lean_apply_2(v_k_1183_, v_ctorName_1184_, v_numFields_1185_);
        return v___x_1186_;
    } else {
        let mut v_numHyps_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_numHyps_1187_ = leanh::lean_ctor_get(v_t_1182_, 0);
        leanh::lean_inc(v_numHyps_1187_);
        leanh::lean_dec_ref_known(v_t_1182_, 1);
        v___x_1188_ = leanh::lean_apply_1(v_k_1183_, v_numHyps_1187_);
        return v___x_1188_;
    }
}
pub unsafe fn l_CasesAltInfo_ctorElim(
    mut v_motive_1189_: *mut leanh::LeanObject,
    mut v_ctorIdx_1190_: *mut leanh::LeanObject,
    mut v_t_1191_: *mut leanh::LeanObject,
    mut v_h_1192_: *mut leanh::LeanObject,
    mut v_k_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1194_ = l_CasesAltInfo_ctorElim___redArg(v_t_1191_, v_k_1193_);
    return v___x_1194_;
}
pub unsafe fn l_CasesAltInfo_ctorElim___boxed(
    mut v_motive_1195_: *mut leanh::LeanObject,
    mut v_ctorIdx_1196_: *mut leanh::LeanObject,
    mut v_t_1197_: *mut leanh::LeanObject,
    mut v_h_1198_: *mut leanh::LeanObject,
    mut v_k_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1200_ = l_CasesAltInfo_ctorElim(
        v_motive_1195_,
        v_ctorIdx_1196_,
        v_t_1197_,
        v_h_1198_,
        v_k_1199_,
    );
    leanh::lean_dec(v_ctorIdx_1196_);
    return v_res_1200_;
}
pub unsafe fn l_CasesAltInfo_ctor_elim___redArg(
    mut v_t_1201_: *mut leanh::LeanObject,
    mut v_ctor_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_CasesAltInfo_ctorElim___redArg(v_t_1201_, v_ctor_1202_);
    return v___x_1203_;
}
pub unsafe fn l_CasesAltInfo_ctor_elim(
    mut v_motive_1204_: *mut leanh::LeanObject,
    mut v_t_1205_: *mut leanh::LeanObject,
    mut v_h_1206_: *mut leanh::LeanObject,
    mut v_ctor_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_CasesAltInfo_ctorElim___redArg(v_t_1205_, v_ctor_1207_);
    return v___x_1208_;
}
pub unsafe fn l_CasesAltInfo_default_elim___redArg(
    mut v_t_1209_: *mut leanh::LeanObject,
    mut v_default_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1211_ = l_CasesAltInfo_ctorElim___redArg(v_t_1209_, v_default_1210_);
    return v___x_1211_;
}
pub unsafe fn l_CasesAltInfo_default_elim(
    mut v_motive_1212_: *mut leanh::LeanObject,
    mut v_t_1213_: *mut leanh::LeanObject,
    mut v_h_1214_: *mut leanh::LeanObject,
    mut v_default_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_CasesAltInfo_ctorElim___redArg(v_t_1213_, v_default_1215_);
    return v___x_1216_;
}
pub unsafe fn l_CasesInfo_numAlts(
    mut v_c_1222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_altNumParams_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_altNumParams_1223_ = leanh::lean_ctor_get(v_c_1222_, 5);
    v___x_1224_ = lean_array_get_size(v_altNumParams_1223_);
    return v___x_1224_;
}
pub unsafe fn l_CasesInfo_numAlts___boxed(
    mut v_c_1225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1226_ = l_CasesInfo_numAlts(v_c_1225_);
    leanh::lean_dec_ref(v_c_1225_);
    return v_res_1226_;
}
pub unsafe fn l_panic___at___00getCasesInfo_x3f_spec__1(
    mut v_msg_1228_: *mut leanh::LeanObject,
    mut v___y_1229_: *mut leanh::LeanObject,
    mut v___y_1230_: *mut leanh::LeanObject,
    mut v___y_1231_: *mut leanh::LeanObject,
    mut v___y_1232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295__overap_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1234_ = l_panic___at___00getCasesInfo_x3f_spec__1___closed__0;
    v___x_6295__overap_1235_ = lean_panic_fn_borrowed(v___f_1234_, v_msg_1228_);
    leanh::lean_inc(v___y_1232_);
    leanh::lean_inc_ref(v___y_1231_);
    leanh::lean_inc(v___y_1230_);
    leanh::lean_inc_ref(v___y_1229_);
    v___x_1236_ = leanh::lean_apply_5(
        v___x_6295__overap_1235_,
        v___y_1229_,
        v___y_1230_,
        v___y_1231_,
        v___y_1232_,
        leanh::lean_box(0),
    );
    return v___x_1236_;
}
pub unsafe fn l_panic___at___00getCasesInfo_x3f_spec__1___boxed(
    mut v_msg_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
    mut v___y_1240_: *mut leanh::LeanObject,
    mut v___y_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_panic___at___00getCasesInfo_x3f_spec__1(
        v_msg_1237_,
        v___y_1238_,
        v___y_1239_,
        v___y_1240_,
        v___y_1241_,
    );
    leanh::lean_dec(v___y_1241_);
    leanh::lean_dec_ref(v___y_1240_);
    leanh::lean_dec(v___y_1239_);
    leanh::lean_dec_ref(v___y_1238_);
    return v_res_1243_;
}
pub unsafe fn l_panic___at___00getCasesInfo_x3f_spec__3(
    mut v_msg_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
    mut v___y_1246_: *mut leanh::LeanObject,
    mut v___y_1247_: *mut leanh::LeanObject,
    mut v___y_1248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317__overap_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1250_ = l_panic___at___00getCasesInfo_x3f_spec__1___closed__0;
    v___x_6317__overap_1251_ = lean_panic_fn_borrowed(v___f_1250_, v_msg_1244_);
    leanh::lean_inc(v___y_1248_);
    leanh::lean_inc_ref(v___y_1247_);
    leanh::lean_inc(v___y_1246_);
    leanh::lean_inc_ref(v___y_1245_);
    v___x_1252_ = leanh::lean_apply_5(
        v___x_6317__overap_1251_,
        v___y_1245_,
        v___y_1246_,
        v___y_1247_,
        v___y_1248_,
        leanh::lean_box(0),
    );
    return v___x_1252_;
}
pub unsafe fn l_panic___at___00getCasesInfo_x3f_spec__3___boxed(
    mut v_msg_1253_: *mut leanh::LeanObject,
    mut v___y_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_panic___at___00getCasesInfo_x3f_spec__3(
        v_msg_1253_,
        v___y_1254_,
        v___y_1255_,
        v___y_1256_,
        v___y_1257_,
    );
    leanh::lean_dec(v___y_1257_);
    leanh::lean_dec_ref(v___y_1256_);
    leanh::lean_dec(v___y_1255_);
    leanh::lean_dec_ref(v___y_1254_);
    return v_res_1259_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0(
    mut v_k_1260_: *mut leanh::LeanObject,
    mut v_b_1261_: *mut leanh::LeanObject,
    mut v_c_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1266_);
    leanh::lean_inc_ref(v___y_1265_);
    leanh::lean_inc(v___y_1264_);
    leanh::lean_inc_ref(v___y_1263_);
    v___x_1268_ = leanh::lean_apply_7(
        v_k_1260_,
        v_b_1261_,
        v_c_1262_,
        v___y_1263_,
        v___y_1264_,
        v___y_1265_,
        v___y_1266_,
        leanh::lean_box(0),
    );
    return v___x_1268_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0___boxed(
    mut v_k_1269_: *mut leanh::LeanObject,
    mut v_b_1270_: *mut leanh::LeanObject,
    mut v_c_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
    mut v___y_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1277_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0(
        v_k_1269_,
        v_b_1270_,
        v_c_1271_,
        v___y_1272_,
        v___y_1273_,
        v___y_1274_,
        v___y_1275_,
    );
    leanh::lean_dec(v___y_1275_);
    leanh::lean_dec_ref(v___y_1274_);
    leanh::lean_dec(v___y_1273_);
    leanh::lean_dec_ref(v___y_1272_);
    return v_res_1277_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(
    mut v_type_1278_: *mut leanh::LeanObject,
    mut v_k_1279_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1280_: u8,
    mut v___y_1281_: *mut leanh::LeanObject,
    mut v___y_1282_: *mut leanh::LeanObject,
    mut v___y_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: u8 = 0;
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1293_: u8 = 0;
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut v_a_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1286_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_1286_, 0, v_k_1279_);
                v___x_1287_ = 0;
                v___x_1288_ = leanh::lean_box(0);
                v___x_1289_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        leanh::lean_box(0),
                        v___x_1287_,
                        v___x_1288_,
                        v_type_1278_,
                        v___f_1286_,
                        v_cleanupAnnotations_1280_,
                        v___x_1287_,
                        v___y_1281_,
                        v___y_1282_,
                        v___y_1283_,
                        v___y_1284_,
                    );
                if leanh::lean_obj_tag(v___x_1289_) == 0 {
                    v_a_1290_ = leanh::lean_ctor_get(v___x_1289_, 0);
                    v_isSharedCheck_1297_ = (!leanh::lean_is_exclusive(v___x_1289_)) as u8;
                    if v_isSharedCheck_1297_ == 0 {
                        v___x_1292_ = v___x_1289_;
                        v_isShared_1293_ = v_isSharedCheck_1297_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1290_);
                        leanh::lean_dec(v___x_1289_);
                        v___x_1292_ = leanh::lean_box(0);
                        v_isShared_1293_ = v_isSharedCheck_1297_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1298_ = leanh::lean_ctor_get(v___x_1289_, 0);
                    v_isSharedCheck_1305_ = (!leanh::lean_is_exclusive(v___x_1289_)) as u8;
                    if v_isSharedCheck_1305_ == 0 {
                        v___x_1300_ = v___x_1289_;
                        v_isShared_1301_ = v_isSharedCheck_1305_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1298_);
                        leanh::lean_dec(v___x_1289_);
                        v___x_1300_ = leanh::lean_box(0);
                        v_isShared_1301_ = v_isSharedCheck_1305_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1293_ == 0 {
                    v___x_1295_ = v___x_1292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
                    v___x_1295_ = v_reuseFailAlloc_1296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1295_;
            }
            3 => {
                if v_isShared_1301_ == 0 {
                    v___x_1303_ = v___x_1300_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
                    v___x_1303_ = v_reuseFailAlloc_1304_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg___boxed(
    mut v_type_1306_: *mut leanh::LeanObject,
    mut v_k_1307_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
    mut v___y_1311_: *mut leanh::LeanObject,
    mut v___y_1312_: *mut leanh::LeanObject,
    mut v___y_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1314_: u8 = 0;
    let mut v_res_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1314_ = (leanh::lean_unbox(v_cleanupAnnotations_1308_) as u8);
    v_res_1315_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(
        v_type_1306_,
        v_k_1307_,
        v_cleanupAnnotations_boxed_1314_,
        v___y_1309_,
        v___y_1310_,
        v___y_1311_,
        v___y_1312_,
    );
    leanh::lean_dec(v___y_1312_);
    leanh::lean_dec_ref(v___y_1311_);
    leanh::lean_dec(v___y_1310_);
    leanh::lean_dec_ref(v___y_1309_);
    return v_res_1315_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6(
    mut v_00_u03b1_1316_: *mut leanh::LeanObject,
    mut v_type_1317_: *mut leanh::LeanObject,
    mut v_k_1318_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1319_: u8,
    mut v___y_1320_: *mut leanh::LeanObject,
    mut v___y_1321_: *mut leanh::LeanObject,
    mut v___y_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(
        v_type_1317_,
        v_k_1318_,
        v_cleanupAnnotations_1319_,
        v___y_1320_,
        v___y_1321_,
        v___y_1322_,
        v___y_1323_,
    );
    return v___x_1325_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___boxed(
    mut v_00_u03b1_1326_: *mut leanh::LeanObject,
    mut v_type_1327_: *mut leanh::LeanObject,
    mut v_k_1328_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1329_: *mut leanh::LeanObject,
    mut v___y_1330_: *mut leanh::LeanObject,
    mut v___y_1331_: *mut leanh::LeanObject,
    mut v___y_1332_: *mut leanh::LeanObject,
    mut v___y_1333_: *mut leanh::LeanObject,
    mut v___y_1334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1335_: u8 = 0;
    let mut v_res_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1335_ = (leanh::lean_unbox(v_cleanupAnnotations_1329_) as u8);
    v_res_1336_ = l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6(
        v_00_u03b1_1326_,
        v_type_1327_,
        v_k_1328_,
        v_cleanupAnnotations_boxed_1335_,
        v___y_1330_,
        v___y_1331_,
        v___y_1332_,
        v___y_1333_,
    );
    leanh::lean_dec(v___y_1333_);
    leanh::lean_dec_ref(v___y_1332_);
    leanh::lean_dec(v___y_1331_);
    leanh::lean_dec_ref(v___y_1330_);
    return v_res_1336_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10(
    mut v_msgData_1337_: *mut leanh::LeanObject,
    mut v___y_1338_: *mut leanh::LeanObject,
    mut v___y_1339_: *mut leanh::LeanObject,
    mut v___y_1340_: *mut leanh::LeanObject,
    mut v___y_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = lean_st_ref_get(v___y_1341_);
    v_env_1344_ = leanh::lean_ctor_get(v___x_1343_, 0);
    leanh::lean_inc_ref(v_env_1344_);
    leanh::lean_dec(v___x_1343_);
    v___x_1345_ = lean_st_ref_get(v___y_1339_);
    v_mctx_1346_ = leanh::lean_ctor_get(v___x_1345_, 0);
    leanh::lean_inc_ref(v_mctx_1346_);
    leanh::lean_dec(v___x_1345_);
    v_lctx_1347_ = leanh::lean_ctor_get(v___y_1338_, 2);
    v_options_1348_ = leanh::lean_ctor_get(v___y_1340_, 2);
    leanh::lean_inc_ref(v_options_1348_);
    leanh::lean_inc_ref(v_lctx_1347_);
    v___x_1349_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1349_, 0, v_env_1344_);
    leanh::lean_ctor_set(v___x_1349_, 1, v_mctx_1346_);
    leanh::lean_ctor_set(v___x_1349_, 2, v_lctx_1347_);
    leanh::lean_ctor_set(v___x_1349_, 3, v_options_1348_);
    v___x_1350_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1350_, 0, v___x_1349_);
    leanh::lean_ctor_set(v___x_1350_, 1, v_msgData_1337_);
    v___x_1351_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1351_, 0, v___x_1350_);
    return v___x_1351_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10___boxed(
    mut v_msgData_1352_: *mut leanh::LeanObject,
    mut v___y_1353_: *mut leanh::LeanObject,
    mut v___y_1354_: *mut leanh::LeanObject,
    mut v___y_1355_: *mut leanh::LeanObject,
    mut v___y_1356_: *mut leanh::LeanObject,
    mut v___y_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10(v_msgData_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
    leanh::lean_dec(v___y_1356_);
    leanh::lean_dec_ref(v___y_1355_);
    leanh::lean_dec(v___y_1354_);
    leanh::lean_dec_ref(v___y_1353_);
    return v_res_1358_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg(
    mut v_msg_1359_: *mut leanh::LeanObject,
    mut v___y_1360_: *mut leanh::LeanObject,
    mut v___y_1361_: *mut leanh::LeanObject,
    mut v___y_1362_: *mut leanh::LeanObject,
    mut v___y_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1365_ = leanh::lean_ctor_get(v___y_1362_, 5);
                v___x_1366_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6_spec__10(v_msg_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
                v_a_1367_ = leanh::lean_ctor_get(v___x_1366_, 0);
                v_isSharedCheck_1375_ = (!leanh::lean_is_exclusive(v___x_1366_)) as u8;
                if v_isSharedCheck_1375_ == 0 {
                    v___x_1369_ = v___x_1366_;
                    v_isShared_1370_ = v_isSharedCheck_1375_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1367_);
                    leanh::lean_dec(v___x_1366_);
                    v___x_1369_ = leanh::lean_box(0);
                    v_isShared_1370_ = v_isSharedCheck_1375_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1365_);
                v___x_1371_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1371_, 0, v_ref_1365_);
                leanh::lean_ctor_set(v___x_1371_, 1, v_a_1367_);
                if v_isShared_1370_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1369_, 1);
                    leanh::lean_ctor_set(v___x_1369_, 0, v___x_1371_);
                    v___x_1373_ = v___x_1369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1374_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
                    v___x_1373_ = v_reuseFailAlloc_1374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg___boxed(
    mut v_msg_1376_: *mut leanh::LeanObject,
    mut v___y_1377_: *mut leanh::LeanObject,
    mut v___y_1378_: *mut leanh::LeanObject,
    mut v___y_1379_: *mut leanh::LeanObject,
    mut v___y_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg(v_msg_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
    leanh::lean_dec(v___y_1380_);
    leanh::lean_dec_ref(v___y_1379_);
    leanh::lean_dec(v___y_1378_);
    leanh::lean_dec_ref(v___y_1377_);
    return v_res_1382_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1383_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_1383_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7(
    mut v_msg_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
    mut v___y_1390_: *mut leanh::LeanObject,
    mut v___y_1391_: *mut leanh::LeanObject,
    mut v___y_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1399_: u8 = 0;
    let mut v_toFunctor_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1406_: u8 = 0;
    let mut v___f_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1423_: u8 = 0;
    let mut v_toFunctor_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___f_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8315__overap_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1449_: u8 = 0;
    let mut v_unused_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1451_: u8 = 0;
    let mut v_unused_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut v_unused_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut v_unused_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1394_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__0);
                v___x_1395_ = l_StateRefT_x27_instMonad___redArg(v___x_1394_);
                v_toApplicative_1396_ = leanh::lean_ctor_get(v___x_1395_, 0);
                v_isSharedCheck_1457_ = (!leanh::lean_is_exclusive(v___x_1395_)) as u8;
                if v_isSharedCheck_1457_ == 0 {
                    v_unused_1458_ = leanh::lean_ctor_get(v___x_1395_, 1);
                    leanh::lean_dec(v_unused_1458_);
                    v___x_1398_ = v___x_1395_;
                    v_isShared_1399_ = v_isSharedCheck_1457_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1396_);
                    leanh::lean_dec(v___x_1395_);
                    v___x_1398_ = leanh::lean_box(0);
                    v_isShared_1399_ = v_isSharedCheck_1457_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1400_ = leanh::lean_ctor_get(v_toApplicative_1396_, 0);
                v_toSeq_1401_ = leanh::lean_ctor_get(v_toApplicative_1396_, 2);
                v_toSeqLeft_1402_ = leanh::lean_ctor_get(v_toApplicative_1396_, 3);
                v_toSeqRight_1403_ = leanh::lean_ctor_get(v_toApplicative_1396_, 4);
                v_isSharedCheck_1455_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1396_)) as u8;
                if v_isSharedCheck_1455_ == 0 {
                    v_unused_1456_ = leanh::lean_ctor_get(v_toApplicative_1396_, 1);
                    leanh::lean_dec(v_unused_1456_);
                    v___x_1405_ = v_toApplicative_1396_;
                    v_isShared_1406_ = v_isSharedCheck_1455_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1403_);
                    leanh::lean_inc(v_toSeqLeft_1402_);
                    leanh::lean_inc(v_toSeq_1401_);
                    leanh::lean_inc(v_toFunctor_1400_);
                    leanh::lean_dec(v_toApplicative_1396_);
                    v___x_1405_ = leanh::lean_box(0);
                    v_isShared_1406_ = v_isSharedCheck_1455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1407_ = l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__1;
                v___f_1408_ = l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__2;
                leanh::lean_inc_ref(v_toFunctor_1400_);
                v___f_1409_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1409_, 0, v_toFunctor_1400_);
                v___f_1410_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1410_, 0, v_toFunctor_1400_);
                v___x_1411_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1411_, 0, v___f_1409_);
                leanh::lean_ctor_set(v___x_1411_, 1, v___f_1410_);
                v___f_1412_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1412_, 0, v_toSeqRight_1403_);
                v___f_1413_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1413_, 0, v_toSeqLeft_1402_);
                v___f_1414_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1414_, 0, v_toSeq_1401_);
                if v_isShared_1406_ == 0 {
                    leanh::lean_ctor_set(v___x_1405_, 4, v___f_1412_);
                    leanh::lean_ctor_set(v___x_1405_, 3, v___f_1413_);
                    leanh::lean_ctor_set(v___x_1405_, 2, v___f_1414_);
                    leanh::lean_ctor_set(v___x_1405_, 1, v___f_1407_);
                    leanh::lean_ctor_set(v___x_1405_, 0, v___x_1411_);
                    v___x_1416_ = v___x_1405_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1454_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___f_1407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 2, v___f_1414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 3, v___f_1413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 4, v___f_1412_);
                    v___x_1416_ = v_reuseFailAlloc_1454_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1399_ == 0 {
                    leanh::lean_ctor_set(v___x_1398_, 1, v___f_1408_);
                    leanh::lean_ctor_set(v___x_1398_, 0, v___x_1416_);
                    v___x_1418_ = v___x_1398_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1453_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___f_1408_);
                    v___x_1418_ = v_reuseFailAlloc_1453_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1419_ = l_StateRefT_x27_instMonad___redArg(v___x_1418_);
                v_toApplicative_1420_ = leanh::lean_ctor_get(v___x_1419_, 0);
                v_isSharedCheck_1451_ = (!leanh::lean_is_exclusive(v___x_1419_)) as u8;
                if v_isSharedCheck_1451_ == 0 {
                    v_unused_1452_ = leanh::lean_ctor_get(v___x_1419_, 1);
                    leanh::lean_dec(v_unused_1452_);
                    v___x_1422_ = v___x_1419_;
                    v_isShared_1423_ = v_isSharedCheck_1451_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1420_);
                    leanh::lean_dec(v___x_1419_);
                    v___x_1422_ = leanh::lean_box(0);
                    v_isShared_1423_ = v_isSharedCheck_1451_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1424_ = leanh::lean_ctor_get(v_toApplicative_1420_, 0);
                v_toSeq_1425_ = leanh::lean_ctor_get(v_toApplicative_1420_, 2);
                v_toSeqLeft_1426_ = leanh::lean_ctor_get(v_toApplicative_1420_, 3);
                v_toSeqRight_1427_ = leanh::lean_ctor_get(v_toApplicative_1420_, 4);
                v_isSharedCheck_1449_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1420_)) as u8;
                if v_isSharedCheck_1449_ == 0 {
                    v_unused_1450_ = leanh::lean_ctor_get(v_toApplicative_1420_, 1);
                    leanh::lean_dec(v_unused_1450_);
                    v___x_1429_ = v_toApplicative_1420_;
                    v_isShared_1430_ = v_isSharedCheck_1449_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1427_);
                    leanh::lean_inc(v_toSeqLeft_1426_);
                    leanh::lean_inc(v_toSeq_1425_);
                    leanh::lean_inc(v_toFunctor_1424_);
                    leanh::lean_dec(v_toApplicative_1420_);
                    v___x_1429_ = leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1449_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1431_ = l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__3;
                v___f_1432_ = l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___closed__4;
                leanh::lean_inc_ref(v_toFunctor_1424_);
                v___f_1433_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1433_, 0, v_toFunctor_1424_);
                v___f_1434_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1434_, 0, v_toFunctor_1424_);
                v___x_1435_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1435_, 0, v___f_1433_);
                leanh::lean_ctor_set(v___x_1435_, 1, v___f_1434_);
                v___f_1436_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1436_, 0, v_toSeqRight_1427_);
                v___f_1437_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1437_, 0, v_toSeqLeft_1426_);
                v___f_1438_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1438_, 0, v_toSeq_1425_);
                if v_isShared_1430_ == 0 {
                    leanh::lean_ctor_set(v___x_1429_, 4, v___f_1436_);
                    leanh::lean_ctor_set(v___x_1429_, 3, v___f_1437_);
                    leanh::lean_ctor_set(v___x_1429_, 2, v___f_1438_);
                    leanh::lean_ctor_set(v___x_1429_, 1, v___f_1431_);
                    leanh::lean_ctor_set(v___x_1429_, 0, v___x_1435_);
                    v___x_1440_ = v___x_1429_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1448_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1435_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___f_1431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 2, v___f_1438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 3, v___f_1437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 4, v___f_1436_);
                    v___x_1440_ = v_reuseFailAlloc_1448_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1423_ == 0 {
                    leanh::lean_ctor_set(v___x_1422_, 1, v___f_1432_);
                    leanh::lean_ctor_set(v___x_1422_, 0, v___x_1440_);
                    v___x_1442_ = v___x_1422_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1447_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___f_1432_);
                    v___x_1442_ = v_reuseFailAlloc_1447_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1443_ = leanh::lean_box(0);
                v___x_1444_ = l_instInhabitedOfMonad___redArg(v___x_1442_, v___x_1443_);
                v___x_8315__overap_1445_ = lean_panic_fn_borrowed(v___x_1444_, v_msg_1388_);
                leanh::lean_dec(v___x_1444_);
                leanh::lean_inc(v___y_1392_);
                leanh::lean_inc_ref(v___y_1391_);
                leanh::lean_inc(v___y_1390_);
                leanh::lean_inc_ref(v___y_1389_);
                v___x_1446_ = leanh::lean_apply_5(
                    v___x_8315__overap_1445_,
                    v___y_1389_,
                    v___y_1390_,
                    v___y_1391_,
                    v___y_1392_,
                    leanh::lean_box(0),
                );
                return v___x_1446_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7___boxed(
    mut v_msg_1459_: *mut leanh::LeanObject,
    mut v___y_1460_: *mut leanh::LeanObject,
    mut v___y_1461_: *mut leanh::LeanObject,
    mut v___y_1462_: *mut leanh::LeanObject,
    mut v___y_1463_: *mut leanh::LeanObject,
    mut v___y_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1465_ = l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7(
        v_msg_1459_,
        v___y_1460_,
        v___y_1461_,
        v___y_1462_,
        v___y_1463_,
    );
    leanh::lean_dec(v___y_1463_);
    leanh::lean_dec_ref(v___y_1462_);
    leanh::lean_dec(v___y_1461_);
    leanh::lean_dec_ref(v___y_1460_);
    return v_res_1465_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__0;
    v___x_1468_ = l_Lean_stringToMessageData(v___x_1467_);
    return v___x_1468_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1470_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__2;
    v___x_1471_ = l_Lean_stringToMessageData(v___x_1470_);
    return v___x_1471_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1475_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6;
    v___x_1476_ = leanh::lean_unsigned_to_nat(11);
    v___x_1477_ = leanh::lean_unsigned_to_nat(122);
    v___x_1478_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__5;
    v___x_1479_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__4;
    v___x_1480_ = l_mkPanicMessageWithDecl(
        v___x_1479_,
        v___x_1478_,
        v___x_1477_,
        v___x_1476_,
        v___x_1475_,
    );
    return v___x_1480_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4(
    mut v_constName_1481_: *mut leanh::LeanObject,
    mut v___y_1482_: *mut leanh::LeanObject,
    mut v___y_1483_: *mut leanh::LeanObject,
    mut v___y_1484_: *mut leanh::LeanObject,
    mut v___y_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: u8 = 0;
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1500_: u8 = 0;
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1515_: u8 = 0;
    let mut v_val_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_a_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1495_ = lean_st_ref_get(v___y_1485_);
                v_env_1496_ = leanh::lean_ctor_get(v___x_1495_, 0);
                leanh::lean_inc_ref(v_env_1496_);
                leanh::lean_dec(v___x_1495_);
                v___x_1497_ = 0;
                leanh::lean_inc(v_constName_1481_);
                v___x_1498_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1496_, v_constName_1481_, v___x_1497_);
                if leanh::lean_obj_tag(v___x_1498_) == 1 {
                    v_val_1499_ = leanh::lean_ctor_get(v___x_1498_, 0);
                    leanh::lean_inc(v_val_1499_);
                    leanh::lean_dec_ref_known(v___x_1498_, 1);
                    v_kind_1500_ = leanh::lean_ctor_get_uint8(
                        v_val_1499_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_1500_ == 6 {
                        v___x_1501_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1499_);
                        if leanh::lean_obj_tag(v___x_1501_) == 6 {
                            leanh::lean_dec(v_constName_1481_);
                            v_val_1502_ = leanh::lean_ctor_get(v___x_1501_, 0);
                            v_isSharedCheck_1509_ =
                                (!leanh::lean_is_exclusive(v___x_1501_)) as u8;
                            if v_isSharedCheck_1509_ == 0 {
                                v___x_1504_ = v___x_1501_;
                                v_isShared_1505_ = v_isSharedCheck_1509_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_1502_);
                                leanh::lean_dec(v___x_1501_);
                                v___x_1504_ = leanh::lean_box(0);
                                v_isShared_1505_ = v_isSharedCheck_1509_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1501_);
                            v___x_1510_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__7);
                            v___x_1511_ = l_panic___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__7(v___x_1510_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
                            if leanh::lean_obj_tag(v___x_1511_) == 0 {
                                v_a_1512_ = leanh::lean_ctor_get(v___x_1511_, 0);
                                v_isSharedCheck_1520_ =
                                    (!leanh::lean_is_exclusive(v___x_1511_)) as u8;
                                if v_isSharedCheck_1520_ == 0 {
                                    v___x_1514_ = v___x_1511_;
                                    v_isShared_1515_ = v_isSharedCheck_1520_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1512_);
                                    leanh::lean_dec(v___x_1511_);
                                    v___x_1514_ = leanh::lean_box(0);
                                    v_isShared_1515_ = v_isSharedCheck_1520_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_constName_1481_);
                                v_a_1521_ = leanh::lean_ctor_get(v___x_1511_, 0);
                                v_isSharedCheck_1528_ =
                                    (!leanh::lean_is_exclusive(v___x_1511_)) as u8;
                                if v_isSharedCheck_1528_ == 0 {
                                    v___x_1523_ = v___x_1511_;
                                    v_isShared_1524_ = v_isSharedCheck_1528_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1521_);
                                    leanh::lean_dec(v___x_1511_);
                                    v___x_1523_ = leanh::lean_box(0);
                                    v_isShared_1524_ = v_isSharedCheck_1528_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_1499_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1498_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1488_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1_once
                    ),
                    _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1,
                );
                v___x_1489_ = 0;
                v___x_1490_ = l_Lean_MessageData_ofConstName(v_constName_1481_, v___x_1489_);
                v___x_1491_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1491_, 0, v___x_1488_);
                leanh::lean_ctor_set(v___x_1491_, 1, v___x_1490_);
                v___x_1492_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3_once
                    ),
                    _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__3,
                );
                v___x_1493_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1493_, 0, v___x_1491_);
                leanh::lean_ctor_set(v___x_1493_, 1, v___x_1492_);
                v___x_1494_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg(v___x_1493_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
                return v___x_1494_;
            }
            2 => {
                if v_isShared_1505_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1504_, 0);
                    v___x_1507_ = v___x_1504_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_val_1502_);
                    v___x_1507_ = v_reuseFailAlloc_1508_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1507_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_1512_) == 0 {
                    leanh::lean_del_object(v___x_1514_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_constName_1481_);
                    v_val_1516_ = leanh::lean_ctor_get(v_a_1512_, 0);
                    leanh::lean_inc(v_val_1516_);
                    leanh::lean_dec_ref_known(v_a_1512_, 1);
                    if v_isShared_1515_ == 0 {
                        leanh::lean_ctor_set(v___x_1514_, 0, v_val_1516_);
                        v___x_1518_ = v___x_1514_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1519_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_val_1516_);
                        v___x_1518_ = v_reuseFailAlloc_1519_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1518_;
            }
            6 => {
                if v_isShared_1524_ == 0 {
                    v___x_1526_ = v___x_1523_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
                    v___x_1526_ = v_reuseFailAlloc_1527_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___boxed(
    mut v_constName_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
    mut v___y_1532_: *mut leanh::LeanObject,
    mut v___y_1533_: *mut leanh::LeanObject,
    mut v___y_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1535_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4(
        v_constName_1529_,
        v___y_1530_,
        v___y_1531_,
        v___y_1532_,
        v___y_1533_,
    );
    leanh::lean_dec(v___y_1533_);
    leanh::lean_dec_ref(v___y_1532_);
    leanh::lean_dec(v___y_1531_);
    leanh::lean_dec_ref(v___y_1530_);
    return v_res_1535_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__2;
    v___x_1540_ = leanh::lean_unsigned_to_nat(10);
    v___x_1541_ = leanh::lean_unsigned_to_nat(71);
    v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1;
    v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0;
    v___x_1544_ = l_mkPanicMessageWithDecl(
        v___x_1543_,
        v___x_1542_,
        v___x_1541_,
        v___x_1540_,
        v___x_1539_,
    );
    return v___x_1544_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1545_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6;
    v___x_1546_ = leanh::lean_unsigned_to_nat(65);
    v___x_1547_ = leanh::lean_unsigned_to_nat(80);
    v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1;
    v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0;
    v___x_1550_ = l_mkPanicMessageWithDecl(
        v___x_1549_,
        v___x_1548_,
        v___x_1547_,
        v___x_1546_,
        v___x_1545_,
    );
    return v___x_1550_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__5;
    v___x_1553_ = leanh::lean_unsigned_to_nat(12);
    v___x_1554_ = leanh::lean_unsigned_to_nat(76);
    v___x_1555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1;
    v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0;
    v___x_1557_ = l_mkPanicMessageWithDecl(
        v___x_1556_,
        v___x_1555_,
        v___x_1554_,
        v___x_1553_,
        v___x_1552_,
    );
    return v___x_1557_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0(
    mut v___x_1558_: *mut leanh::LeanObject,
    mut v_ys_1559_: *mut leanh::LeanObject,
    mut v_mr_1560_: *mut leanh::LeanObject,
    mut v___y_1561_: *mut leanh::LeanObject,
    mut v___y_1562_: *mut leanh::LeanObject,
    mut v___y_1563_: *mut leanh::LeanObject,
    mut v___y_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1566_: u8 = 0;
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v_numFields_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1584_: u8 = 0;
    let mut v_a_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1592_: u8 = 0;
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u8 = 0;
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1566_ = l_Lean_Expr_isApp(v_mr_1560_);
                if v___x_1566_ == 0 {
                    v___x_1567_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__3);
                    v___x_1568_ = l_panic___at___00getCasesInfo_x3f_spec__3(
                        v___x_1567_,
                        v___y_1561_,
                        v___y_1562_,
                        v___y_1563_,
                        v___y_1564_,
                    );
                    return v___x_1568_;
                } else {
                    v___x_1569_ = l_Lean_Expr_appArg_x21(v_mr_1560_);
                    v___x_1570_ = l_Lean_Expr_isFVar(v___x_1569_);
                    if v___x_1570_ == 0 {
                        v___x_1571_ = l_Lean_Expr_getAppFn(v___x_1569_);
                        leanh::lean_dec_ref(v___x_1569_);
                        v___x_1572_ = l_Lean_Expr_constName_x3f(v___x_1571_);
                        leanh::lean_dec_ref(v___x_1571_);
                        if leanh::lean_obj_tag(v___x_1572_) == 1 {
                            v_val_1573_ = leanh::lean_ctor_get(v___x_1572_, 0);
                            leanh::lean_inc_n(v_val_1573_, 2);
                            leanh::lean_dec_ref_known(v___x_1572_, 1);
                            v___x_1574_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4(
                                v_val_1573_,
                                v___y_1561_,
                                v___y_1562_,
                                v___y_1563_,
                                v___y_1564_,
                            );
                            if leanh::lean_obj_tag(v___x_1574_) == 0 {
                                v_a_1575_ = leanh::lean_ctor_get(v___x_1574_, 0);
                                v_isSharedCheck_1584_ =
                                    (!leanh::lean_is_exclusive(v___x_1574_)) as u8;
                                if v_isSharedCheck_1584_ == 0 {
                                    v___x_1577_ = v___x_1574_;
                                    v_isShared_1578_ = v_isSharedCheck_1584_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1575_);
                                    leanh::lean_dec(v___x_1574_);
                                    v___x_1577_ = leanh::lean_box(0);
                                    v_isShared_1578_ = v_isSharedCheck_1584_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_1573_);
                                v_a_1585_ = leanh::lean_ctor_get(v___x_1574_, 0);
                                v_isSharedCheck_1592_ =
                                    (!leanh::lean_is_exclusive(v___x_1574_)) as u8;
                                if v_isSharedCheck_1592_ == 0 {
                                    v___x_1587_ = v___x_1574_;
                                    v_isShared_1588_ = v_isSharedCheck_1592_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1585_);
                                    leanh::lean_dec(v___x_1574_);
                                    v___x_1587_ = leanh::lean_box(0);
                                    v_isShared_1588_ = v_isSharedCheck_1592_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_1572_);
                            v___x_1593_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__4);
                            v___x_1594_ = l_panic___at___00getCasesInfo_x3f_spec__3(
                                v___x_1593_,
                                v___y_1561_,
                                v___y_1562_,
                                v___y_1563_,
                                v___y_1564_,
                            );
                            return v___x_1594_;
                        }
                    } else {
                        v___x_1595_ = lean_expr_eqv(v___x_1569_, v___x_1558_);
                        leanh::lean_dec_ref(v___x_1569_);
                        if v___x_1595_ == 0 {
                            v___x_1596_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__6);
                            v___x_1597_ = l_panic___at___00getCasesInfo_x3f_spec__3(
                                v___x_1596_,
                                v___y_1561_,
                                v___y_1562_,
                                v___y_1563_,
                                v___y_1564_,
                            );
                            return v___x_1597_;
                        } else {
                            v___x_1598_ = lean_array_get_size(v_ys_1559_);
                            v___x_1599_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1599_, 0, v___x_1598_);
                            v___x_1600_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1600_, 0, v___x_1599_);
                            return v___x_1600_;
                        }
                    }
                }
            }
            1 => {
                v_numFields_1579_ = leanh::lean_ctor_get(v_a_1575_, 4);
                leanh::lean_inc(v_numFields_1579_);
                leanh::lean_dec(v_a_1575_);
                v___x_1580_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1580_, 0, v_val_1573_);
                leanh::lean_ctor_set(v___x_1580_, 1, v_numFields_1579_);
                if v_isShared_1578_ == 0 {
                    leanh::lean_ctor_set(v___x_1577_, 0, v___x_1580_);
                    v___x_1582_ = v___x_1577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1583_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
                    v___x_1582_ = v_reuseFailAlloc_1583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1582_;
            }
            3 => {
                if v_isShared_1588_ == 0 {
                    v___x_1590_ = v___x_1587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1591_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
                    v___x_1590_ = v_reuseFailAlloc_1591_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___boxed(
    mut v___x_1601_: *mut leanh::LeanObject,
    mut v_ys_1602_: *mut leanh::LeanObject,
    mut v_mr_1603_: *mut leanh::LeanObject,
    mut v___y_1604_: *mut leanh::LeanObject,
    mut v___y_1605_: *mut leanh::LeanObject,
    mut v___y_1606_: *mut leanh::LeanObject,
    mut v___y_1607_: *mut leanh::LeanObject,
    mut v___y_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0(v___x_1601_, v_ys_1602_, v_mr_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
    leanh::lean_dec(v___y_1607_);
    leanh::lean_dec_ref(v___y_1606_);
    leanh::lean_dec(v___y_1605_);
    leanh::lean_dec_ref(v___y_1604_);
    leanh::lean_dec_ref(v_mr_1603_);
    leanh::lean_dec_ref(v_ys_1602_);
    leanh::lean_dec_ref(v___x_1601_);
    return v_res_1609_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8(
    mut v_val_1610_: *mut leanh::LeanObject,
    mut v_a_1611_: *mut leanh::LeanObject,
    mut v___x_1612_: *mut leanh::LeanObject,
    mut v_sz_1613_: usize,
    mut v_i_1614_: usize,
    mut v_bs_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
    mut v___y_1617_: *mut leanh::LeanObject,
    mut v___y_1618_: *mut leanh::LeanObject,
    mut v___y_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: usize = 0;
    let mut v___x_1636_: usize = 0;
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1621_ = lean_usize_dec_lt(v_i_1614_, v_sz_1613_);
                if v___x_1621_ == 0 {
                    leanh::lean_dec_ref(v___x_1612_);
                    v___x_1622_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1622_, 0, v_bs_1615_);
                    return v___x_1622_;
                } else {
                    leanh::lean_inc_ref(v___x_1612_);
                    v___f_1623_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    leanh::lean_closure_set(v___f_1623_, 0, v___x_1612_);
                    v___x_1624_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1625_ = l_Lean_instInhabitedExpr;
                    v_v_1626_ = lean_array_uget_borrowed(v_bs_1615_, v_i_1614_);
                    v___x_1627_ = lean_nat_sub(v_v_1626_, v_val_1610_);
                    v___x_1628_ = lean_nat_sub(v___x_1627_, v___x_1624_);
                    leanh::lean_dec(v___x_1627_);
                    v___x_1629_ = lean_array_get_borrowed(v___x_1625_, v_a_1611_, v___x_1628_);
                    leanh::lean_dec(v___x_1628_);
                    v___x_1630_ = 0;
                    leanh::lean_inc(v___x_1629_);
                    v___x_1631_ =
                        l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(
                            v___x_1629_,
                            v___f_1623_,
                            v___x_1630_,
                            v___y_1616_,
                            v___y_1617_,
                            v___y_1618_,
                            v___y_1619_,
                        );
                    if leanh::lean_obj_tag(v___x_1631_) == 0 {
                        v_a_1632_ = leanh::lean_ctor_get(v___x_1631_, 0);
                        leanh::lean_inc(v_a_1632_);
                        leanh::lean_dec_ref_known(v___x_1631_, 1);
                        v___x_1633_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1634_ = lean_array_uset(v_bs_1615_, v_i_1614_, v___x_1633_);
                        v___x_1635_ = 1usize;
                        v___x_1636_ = lean_usize_add(v_i_1614_, v___x_1635_);
                        v___x_1637_ = lean_array_uset(v_bs_x27_1634_, v_i_1614_, v_a_1632_);
                        v_i_1614_ = v___x_1636_;
                        v_bs_1615_ = v___x_1637_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_1615_);
                        leanh::lean_dec_ref(v___x_1612_);
                        v_a_1639_ = leanh::lean_ctor_get(v___x_1631_, 0);
                        v_isSharedCheck_1646_ =
                            (!leanh::lean_is_exclusive(v___x_1631_)) as u8;
                        if v_isSharedCheck_1646_ == 0 {
                            v___x_1641_ = v___x_1631_;
                            v_isShared_1642_ = v_isSharedCheck_1646_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1639_);
                            leanh::lean_dec(v___x_1631_);
                            v___x_1641_ = leanh::lean_box(0);
                            v_isShared_1642_ = v_isSharedCheck_1646_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1642_ == 0 {
                    v___x_1644_ = v___x_1641_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
                    v___x_1644_ = v_reuseFailAlloc_1645_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___boxed(
    mut v_val_1647_: *mut leanh::LeanObject,
    mut v_a_1648_: *mut leanh::LeanObject,
    mut v___x_1649_: *mut leanh::LeanObject,
    mut v_sz_1650_: *mut leanh::LeanObject,
    mut v_i_1651_: *mut leanh::LeanObject,
    mut v_bs_1652_: *mut leanh::LeanObject,
    mut v___y_1653_: *mut leanh::LeanObject,
    mut v___y_1654_: *mut leanh::LeanObject,
    mut v___y_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1658_: usize = 0;
    let mut v_i_boxed_1659_: usize = 0;
    let mut v_res_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1658_ = leanh::lean_unbox_usize(v_sz_1650_);
    leanh::lean_dec(v_sz_1650_);
    v_i_boxed_1659_ = leanh::lean_unbox_usize(v_i_1651_);
    leanh::lean_dec(v_i_1651_);
    v_res_1660_ =
        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8(
            v_val_1647_,
            v_a_1648_,
            v___x_1649_,
            v_sz_boxed_1658_,
            v_i_boxed_1659_,
            v_bs_1652_,
            v___y_1653_,
            v___y_1654_,
            v___y_1655_,
            v___y_1656_,
        );
    leanh::lean_dec(v___y_1656_);
    leanh::lean_dec_ref(v___y_1655_);
    leanh::lean_dec(v___y_1654_);
    leanh::lean_dec_ref(v___y_1653_);
    leanh::lean_dec_ref(v_a_1648_);
    leanh::lean_dec(v_val_1647_);
    return v_res_1660_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7(
    mut v_xs_1661_: *mut leanh::LeanObject,
    mut v_v_1662_: *mut leanh::LeanObject,
    mut v_i_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: u8 = 0;
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1664_ = lean_array_get_size(v_xs_1661_);
                v___x_1665_ = lean_nat_dec_lt(v_i_1663_, v___x_1664_);
                if v___x_1665_ == 0 {
                    leanh::lean_dec(v_i_1663_);
                    v___x_1666_ = leanh::lean_box(0);
                    return v___x_1666_;
                } else {
                    v___x_1667_ = lean_array_fget_borrowed(v_xs_1661_, v_i_1663_);
                    v___x_1668_ = lean_expr_eqv(v___x_1667_, v_v_1662_);
                    if v___x_1668_ == 0 {
                        v___x_1669_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1670_ = lean_nat_add(v_i_1663_, v___x_1669_);
                        leanh::lean_dec(v_i_1663_);
                        v_i_1663_ = v___x_1670_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1672_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1672_, 0, v_i_1663_);
                        return v___x_1672_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7___boxed(
    mut v_xs_1673_: *mut leanh::LeanObject,
    mut v_v_1674_: *mut leanh::LeanObject,
    mut v_i_1675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1676_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7(v_xs_1673_, v_v_1674_, v_i_1675_);
    leanh::lean_dec_ref(v_v_1674_);
    leanh::lean_dec_ref(v_xs_1673_);
    return v_res_1676_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3(
    mut v_xs_1677_: *mut leanh::LeanObject,
    mut v_v_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1679_ = leanh::lean_unsigned_to_nat(0);
    v___x_1680_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3_spec__7(v_xs_1677_, v_v_1678_, v___x_1679_);
    return v___x_1680_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3___boxed(
    mut v_xs_1681_: *mut leanh::LeanObject,
    mut v_v_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1683_ =
        l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3(
            v_xs_1681_, v_v_1682_,
        );
    leanh::lean_dec_ref(v_v_1682_);
    leanh::lean_dec_ref(v_xs_1681_);
    return v_res_1683_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2(
    mut v_xs_1684_: *mut leanh::LeanObject,
    mut v_v_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1691_: u8 = 0;
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1686_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2_spec__3(v_xs_1684_, v_v_1685_);
                if leanh::lean_obj_tag(v___x_1686_) == 0 {
                    v___x_1687_ = leanh::lean_box(0);
                    return v___x_1687_;
                } else {
                    v_val_1688_ = leanh::lean_ctor_get(v___x_1686_, 0);
                    v_isSharedCheck_1695_ = (!leanh::lean_is_exclusive(v___x_1686_)) as u8;
                    if v_isSharedCheck_1695_ == 0 {
                        v___x_1690_ = v___x_1686_;
                        v_isShared_1691_ = v_isSharedCheck_1695_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1688_);
                        leanh::lean_dec(v___x_1686_);
                        v___x_1690_ = leanh::lean_box(0);
                        v_isShared_1691_ = v_isSharedCheck_1695_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1691_ == 0 {
                    v___x_1693_ = v___x_1690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1694_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_val_1688_);
                    v___x_1693_ = v_reuseFailAlloc_1694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2___boxed(
    mut v_xs_1696_: *mut leanh::LeanObject,
    mut v_v_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1698_ = l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2(v_xs_1696_, v_v_1697_);
    leanh::lean_dec_ref(v_v_1697_);
    leanh::lean_dec_ref(v_xs_1696_);
    return v_res_1698_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5(
    mut v_sz_1699_: usize,
    mut v_i_1700_: usize,
    mut v_bs_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
    mut v___y_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: usize = 0;
    let mut v___x_1715_: usize = 0;
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1721_: u8 = 0;
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1707_ = lean_usize_dec_lt(v_i_1700_, v_sz_1699_);
                if v___x_1707_ == 0 {
                    v___x_1708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1708_, 0, v_bs_1701_);
                    return v___x_1708_;
                } else {
                    v_v_1709_ = lean_array_uget_borrowed(v_bs_1701_, v_i_1700_);
                    leanh::lean_inc(v___y_1705_);
                    leanh::lean_inc_ref(v___y_1704_);
                    leanh::lean_inc(v___y_1703_);
                    leanh::lean_inc_ref(v___y_1702_);
                    leanh::lean_inc(v_v_1709_);
                    v___x_1710_ = lean_infer_type(
                        v_v_1709_,
                        v___y_1702_,
                        v___y_1703_,
                        v___y_1704_,
                        v___y_1705_,
                    );
                    if leanh::lean_obj_tag(v___x_1710_) == 0 {
                        v_a_1711_ = leanh::lean_ctor_get(v___x_1710_, 0);
                        leanh::lean_inc(v_a_1711_);
                        leanh::lean_dec_ref_known(v___x_1710_, 1);
                        v___x_1712_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1713_ = lean_array_uset(v_bs_1701_, v_i_1700_, v___x_1712_);
                        v___x_1714_ = 1usize;
                        v___x_1715_ = lean_usize_add(v_i_1700_, v___x_1714_);
                        v___x_1716_ = lean_array_uset(v_bs_x27_1713_, v_i_1700_, v_a_1711_);
                        v_i_1700_ = v___x_1715_;
                        v_bs_1701_ = v___x_1716_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_1701_);
                        v_a_1718_ = leanh::lean_ctor_get(v___x_1710_, 0);
                        v_isSharedCheck_1725_ =
                            (!leanh::lean_is_exclusive(v___x_1710_)) as u8;
                        if v_isSharedCheck_1725_ == 0 {
                            v___x_1720_ = v___x_1710_;
                            v_isShared_1721_ = v_isSharedCheck_1725_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1718_);
                            leanh::lean_dec(v___x_1710_);
                            v___x_1720_ = leanh::lean_box(0);
                            v_isShared_1721_ = v_isSharedCheck_1725_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1721_ == 0 {
                    v___x_1723_ = v___x_1720_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
                    v___x_1723_ = v_reuseFailAlloc_1724_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5___boxed(
    mut v_sz_1726_: *mut leanh::LeanObject,
    mut v_i_1727_: *mut leanh::LeanObject,
    mut v_bs_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
    mut v___y_1731_: *mut leanh::LeanObject,
    mut v___y_1732_: *mut leanh::LeanObject,
    mut v___y_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1734_: usize = 0;
    let mut v_i_boxed_1735_: usize = 0;
    let mut v_res_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1734_ = leanh::lean_unbox_usize(v_sz_1726_);
    leanh::lean_dec(v_sz_1726_);
    v_i_boxed_1735_ = leanh::lean_unbox_usize(v_i_1727_);
    leanh::lean_dec(v_i_1727_);
    v_res_1736_ =
        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5(
            v_sz_boxed_1734_,
            v_i_boxed_1735_,
            v_bs_1728_,
            v___y_1729_,
            v___y_1730_,
            v___y_1731_,
            v___y_1732_,
        );
    leanh::lean_dec(v___y_1732_);
    leanh::lean_dec_ref(v___y_1731_);
    leanh::lean_dec(v___y_1730_);
    leanh::lean_dec_ref(v___y_1729_);
    return v_res_1736_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7___redArg(
    mut v_a_1737_: *mut leanh::LeanObject,
    mut v_b_1738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_next_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v_val_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1747_: u8 = 0;
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1759_: u8 = 0;
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut v_unused_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_next_1739_ = leanh::lean_ctor_get(v_a_1737_, 0);
                leanh::lean_inc(v_next_1739_);
                if leanh::lean_obj_tag(v_next_1739_) == 0 {
                    leanh::lean_dec_ref(v_a_1737_);
                    return v_b_1738_;
                } else {
                    v_upperBound_1740_ = leanh::lean_ctor_get(v_a_1737_, 1);
                    v_isSharedCheck_1760_ = (!leanh::lean_is_exclusive(v_a_1737_)) as u8;
                    if v_isSharedCheck_1760_ == 0 {
                        v_unused_1761_ = leanh::lean_ctor_get(v_a_1737_, 0);
                        leanh::lean_dec(v_unused_1761_);
                        v___x_1742_ = v_a_1737_;
                        v_isShared_1743_ = v_isSharedCheck_1760_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_upperBound_1740_);
                        leanh::lean_dec(v_a_1737_);
                        v___x_1742_ = leanh::lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1760_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1744_ = leanh::lean_ctor_get(v_next_1739_, 0);
                v_isSharedCheck_1759_ = (!leanh::lean_is_exclusive(v_next_1739_)) as u8;
                if v_isSharedCheck_1759_ == 0 {
                    v___x_1746_ = v_next_1739_;
                    v_isShared_1747_ = v_isSharedCheck_1759_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1744_);
                    leanh::lean_dec(v_next_1739_);
                    v___x_1746_ = leanh::lean_box(0);
                    v_isShared_1747_ = v_isSharedCheck_1759_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1748_ = lean_nat_dec_lt(v_val_1744_, v_upperBound_1740_);
                if v___x_1748_ == 0 {
                    leanh::lean_del_object(v___x_1746_);
                    leanh::lean_dec(v_val_1744_);
                    leanh::lean_del_object(v___x_1742_);
                    leanh::lean_dec(v_upperBound_1740_);
                    return v_b_1738_;
                } else {
                    v___x_1749_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1750_ = lean_nat_add(v_val_1744_, v___x_1749_);
                    if v_isShared_1747_ == 0 {
                        leanh::lean_ctor_set(v___x_1746_, 0, v___x_1750_);
                        v___x_1752_ = v___x_1746_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1750_);
                        v___x_1752_ = v_reuseFailAlloc_1758_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1743_ == 0 {
                    leanh::lean_ctor_set(v___x_1742_, 0, v___x_1752_);
                    v___x_1754_ = v___x_1742_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_upperBound_1740_);
                    v___x_1754_ = v_reuseFailAlloc_1757_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1755_ = lean_array_push(v_b_1738_, v_val_1744_);
                v_a_1737_ = v___x_1754_;
                v_b_1738_ = v___x_1755_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_getCasesInfo_x3f___lam__0___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_getCasesInfo_x3f___lam__0___closed__0;
    v___x_1764_ = leanh::lean_unsigned_to_nat(6);
    v___x_1765_ = leanh::lean_unsigned_to_nat(60);
    v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1;
    v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0;
    v___x_1768_ = l_mkPanicMessageWithDecl(
        v___x_1767_,
        v___x_1766_,
        v___x_1765_,
        v___x_1764_,
        v___x_1763_,
    );
    return v___x_1768_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___lam__0___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = l_getCasesInfo_x3f___lam__0___closed__2;
    v___x_1771_ = leanh::lean_unsigned_to_nat(6);
    v___x_1772_ = leanh::lean_unsigned_to_nat(61);
    v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1;
    v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0;
    v___x_1775_ = l_mkPanicMessageWithDecl(
        v___x_1774_,
        v___x_1773_,
        v___x_1772_,
        v___x_1771_,
        v___x_1770_,
    );
    return v___x_1775_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___lam__0___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_getCasesInfo_x3f___lam__0___closed__4;
    v___x_1778_ = leanh::lean_unsigned_to_nat(6);
    v___x_1779_ = leanh::lean_unsigned_to_nat(62);
    v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1;
    v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0;
    v___x_1782_ = l_mkPanicMessageWithDecl(
        v___x_1781_,
        v___x_1780_,
        v___x_1779_,
        v___x_1778_,
        v___x_1777_,
    );
    return v___x_1782_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___lam__0___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1785_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6;
    v___x_1786_ = leanh::lean_unsigned_to_nat(76);
    v___x_1787_ = leanh::lean_unsigned_to_nat(64);
    v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1;
    v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0;
    v___x_1790_ = l_mkPanicMessageWithDecl(
        v___x_1789_,
        v___x_1788_,
        v___x_1787_,
        v___x_1786_,
        v___x_1785_,
    );
    return v___x_1790_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___lam__0___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__6;
    v___x_1792_ = leanh::lean_unsigned_to_nat(49);
    v___x_1793_ = leanh::lean_unsigned_to_nat(63);
    v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__1;
    v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8___lam__0___closed__0;
    v___x_1796_ = l_mkPanicMessageWithDecl(
        v___x_1795_,
        v___x_1794_,
        v___x_1793_,
        v___x_1792_,
        v___x_1791_,
    );
    return v___x_1796_;
}
pub unsafe fn l_getCasesInfo_x3f___lam__0(
    mut v_declName_1797_: *mut leanh::LeanObject,
    mut v_xs_1798_: *mut leanh::LeanObject,
    mut v_r_1799_: *mut leanh::LeanObject,
    mut v___y_1800_: *mut leanh::LeanObject,
    mut v___y_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1820_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1835_: usize = 0;
    let mut v___x_1836_: usize = 0;
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1848_: usize = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1861_: u8 = 0;
    let mut v_a_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1865_: u8 = 0;
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_reuseFailAlloc_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1882_: u8 = 0;
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_isSharedCheck_1887_: u8 = 0;
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1893_: u8 = 0;
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_isSharedCheck_1898_: u8 = 0;
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1805_ = l_Lean_Expr_isApp(v_r_1799_);
                if v___x_1805_ == 0 {
                    leanh::lean_dec(v_declName_1797_);
                    v___x_1806_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___lam__0___closed__1_once),
                        _init_l_getCasesInfo_x3f___lam__0___closed__1,
                    );
                    v___x_1807_ = l_panic___at___00getCasesInfo_x3f_spec__1(
                        v___x_1806_,
                        v___y_1800_,
                        v___y_1801_,
                        v___y_1802_,
                        v___y_1803_,
                    );
                    return v___x_1807_;
                } else {
                    v___x_1808_ = l_Lean_Expr_appArg_x21(v_r_1799_);
                    v___x_1809_ = l_Lean_Expr_isFVar(v___x_1808_);
                    if v___x_1809_ == 0 {
                        leanh::lean_dec_ref(v___x_1808_);
                        leanh::lean_dec(v_declName_1797_);
                        v___x_1810_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_getCasesInfo_x3f___lam__0___closed__3),
                            core::ptr::addr_of_mut!(l_getCasesInfo_x3f___lam__0___closed__3_once),
                            _init_l_getCasesInfo_x3f___lam__0___closed__3,
                        );
                        v___x_1811_ = l_panic___at___00getCasesInfo_x3f_spec__1(
                            v___x_1810_,
                            v___y_1800_,
                            v___y_1801_,
                            v___y_1802_,
                            v___y_1803_,
                        );
                        return v___x_1811_;
                    } else {
                        v___x_1812_ = l_Lean_Expr_getAppFn(v_r_1799_);
                        v___x_1813_ = l_Lean_Expr_isFVar(v___x_1812_);
                        if v___x_1813_ == 0 {
                            leanh::lean_dec_ref(v___x_1812_);
                            leanh::lean_dec_ref(v___x_1808_);
                            leanh::lean_dec(v_declName_1797_);
                            v___x_1814_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_getCasesInfo_x3f___lam__0___closed__5),
                                core::ptr::addr_of_mut!(
                                    l_getCasesInfo_x3f___lam__0___closed__5_once
                                ),
                                _init_l_getCasesInfo_x3f___lam__0___closed__5,
                            );
                            v___x_1815_ = l_panic___at___00getCasesInfo_x3f_spec__1(
                                v___x_1814_,
                                v___y_1800_,
                                v___y_1801_,
                                v___y_1802_,
                                v___y_1803_,
                            );
                            return v___x_1815_;
                        } else {
                            v___x_1816_ = l_Array_idxOf_x3f___at___00getCasesInfo_x3f_spec__2(
                                v_xs_1798_,
                                v___x_1808_,
                            );
                            leanh::lean_dec_ref(v___x_1808_);
                            if leanh::lean_obj_tag(v___x_1816_) == 1 {
                                v_val_1817_ = leanh::lean_ctor_get(v___x_1816_, 0);
                                v_isSharedCheck_1898_ =
                                    (!leanh::lean_is_exclusive(v___x_1816_)) as u8;
                                if v_isSharedCheck_1898_ == 0 {
                                    v___x_1819_ = v___x_1816_;
                                    v_isShared_1820_ = v_isSharedCheck_1898_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1817_);
                                    leanh::lean_dec(v___x_1816_);
                                    v___x_1819_ = leanh::lean_box(0);
                                    v_isShared_1820_ = v_isSharedCheck_1898_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_1816_);
                                leanh::lean_dec_ref(v___x_1812_);
                                leanh::lean_dec(v_declName_1797_);
                                v___x_1899_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_getCasesInfo_x3f___lam__0___closed__8
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_getCasesInfo_x3f___lam__0___closed__8_once
                                    ),
                                    _init_l_getCasesInfo_x3f___lam__0___closed__8,
                                );
                                v___x_1900_ = l_panic___at___00getCasesInfo_x3f_spec__1(
                                    v___x_1899_,
                                    v___y_1800_,
                                    v___y_1801_,
                                    v___y_1802_,
                                    v___y_1803_,
                                );
                                return v___x_1900_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1821_ = l_Lean_instInhabitedExpr;
                v___x_1822_ = lean_array_get_borrowed(v___x_1821_, v_xs_1798_, v_val_1817_);
                leanh::lean_inc(v___y_1803_);
                leanh::lean_inc_ref(v___y_1802_);
                leanh::lean_inc(v___y_1801_);
                leanh::lean_inc_ref(v___y_1800_);
                leanh::lean_inc(v___x_1822_);
                v___x_1823_ = lean_infer_type(
                    v___x_1822_,
                    v___y_1800_,
                    v___y_1801_,
                    v___y_1802_,
                    v___y_1803_,
                );
                if leanh::lean_obj_tag(v___x_1823_) == 0 {
                    v_a_1824_ = leanh::lean_ctor_get(v___x_1823_, 0);
                    leanh::lean_inc(v_a_1824_);
                    leanh::lean_dec_ref_known(v___x_1823_, 1);
                    v___x_1825_ = l_Lean_Expr_getAppFn(v_a_1824_);
                    leanh::lean_dec(v_a_1824_);
                    v___x_1826_ = l_Lean_Expr_constName_x3f(v___x_1825_);
                    leanh::lean_dec_ref(v___x_1825_);
                    if leanh::lean_obj_tag(v___x_1826_) == 1 {
                        v_val_1827_ = leanh::lean_ctor_get(v___x_1826_, 0);
                        v_isSharedCheck_1887_ =
                            (!leanh::lean_is_exclusive(v___x_1826_)) as u8;
                        if v_isSharedCheck_1887_ == 0 {
                            v___x_1829_ = v___x_1826_;
                            v_isShared_1830_ = v_isSharedCheck_1887_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1827_);
                            leanh::lean_dec(v___x_1826_);
                            v___x_1829_ = leanh::lean_box(0);
                            v_isShared_1830_ = v_isSharedCheck_1887_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1826_);
                        leanh::lean_del_object(v___x_1819_);
                        leanh::lean_dec(v_val_1817_);
                        leanh::lean_dec_ref(v___x_1812_);
                        leanh::lean_dec(v_declName_1797_);
                        v___x_1888_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_getCasesInfo_x3f___lam__0___closed__7),
                            core::ptr::addr_of_mut!(l_getCasesInfo_x3f___lam__0___closed__7_once),
                            _init_l_getCasesInfo_x3f___lam__0___closed__7,
                        );
                        v___x_1889_ = l_panic___at___00getCasesInfo_x3f_spec__1(
                            v___x_1888_,
                            v___y_1800_,
                            v___y_1801_,
                            v___y_1802_,
                            v___y_1803_,
                        );
                        return v___x_1889_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1819_);
                    leanh::lean_dec(v_val_1817_);
                    leanh::lean_dec_ref(v___x_1812_);
                    leanh::lean_dec(v_declName_1797_);
                    v_a_1890_ = leanh::lean_ctor_get(v___x_1823_, 0);
                    v_isSharedCheck_1897_ = (!leanh::lean_is_exclusive(v___x_1823_)) as u8;
                    if v_isSharedCheck_1897_ == 0 {
                        v___x_1892_ = v___x_1823_;
                        v_isShared_1893_ = v_isSharedCheck_1897_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1890_);
                        leanh::lean_dec(v___x_1823_);
                        v___x_1892_ = leanh::lean_box(0);
                        v_isShared_1893_ = v_isSharedCheck_1897_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1831_ = lean_array_get_size(v_xs_1798_);
                v___x_1832_ = leanh::lean_unsigned_to_nat(1);
                v___x_1833_ = lean_nat_add(v_val_1817_, v___x_1832_);
                v___x_1834_ = l_Array_extract___redArg(v_xs_1798_, v___x_1833_, v___x_1831_);
                v_sz_1835_ = lean_array_size(v___x_1834_);
                v___x_1836_ = 0usize;
                v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__5(v_sz_1835_, v___x_1836_, v___x_1834_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
                if leanh::lean_obj_tag(v___x_1837_) == 0 {
                    v_a_1838_ = leanh::lean_ctor_get(v___x_1837_, 0);
                    leanh::lean_inc(v_a_1838_);
                    leanh::lean_dec_ref_known(v___x_1837_, 1);
                    v___x_1871_ = lean_array_get_size(v_a_1838_);
                    v___x_1872_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1873_ = lean_nat_dec_eq(v___x_1871_, v___x_1872_);
                    if v___x_1873_ == 0 {
                        if v___x_1813_ == 0 {
                            leanh::lean_dec_ref(v___x_1812_);
                            v___y_1840_ = v___x_1832_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1874_ =
                                lean_array_get_borrowed(v___x_1821_, v_a_1838_, v___x_1872_);
                            v___x_1875_ = l_Lean_Expr_getForallBody(v___x_1874_);
                            v___x_1876_ = l_Lean_Expr_getAppFn(v___x_1875_);
                            leanh::lean_dec_ref(v___x_1875_);
                            v___x_1877_ = lean_expr_eqv(v___x_1876_, v___x_1812_);
                            leanh::lean_dec_ref(v___x_1812_);
                            leanh::lean_dec_ref(v___x_1876_);
                            if v___x_1877_ == 0 {
                                v___x_1878_ = leanh::lean_unsigned_to_nat(2);
                                v___y_1840_ = v___x_1878_;
                                state = 3;
                                continue;
                            } else {
                                v___y_1840_ = v___x_1832_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1812_);
                        v___y_1840_ = v___x_1832_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1829_);
                    leanh::lean_dec(v_val_1827_);
                    leanh::lean_del_object(v___x_1819_);
                    leanh::lean_dec(v_val_1817_);
                    leanh::lean_dec_ref(v___x_1812_);
                    leanh::lean_dec(v_declName_1797_);
                    v_a_1879_ = leanh::lean_ctor_get(v___x_1837_, 0);
                    v_isSharedCheck_1886_ = (!leanh::lean_is_exclusive(v___x_1837_)) as u8;
                    if v_isSharedCheck_1886_ == 0 {
                        v___x_1881_ = v___x_1837_;
                        v_isShared_1882_ = v_isSharedCheck_1886_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1879_);
                        leanh::lean_dec(v___x_1837_);
                        v___x_1881_ = leanh::lean_box(0);
                        v_isShared_1882_ = v_isSharedCheck_1886_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1841_ = lean_nat_add(v_val_1817_, v___y_1840_);
                leanh::lean_inc(v___x_1841_);
                v___x_1842_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1842_, 0, v___x_1841_);
                leanh::lean_ctor_set(v___x_1842_, 1, v___x_1831_);
                if v_isShared_1830_ == 0 {
                    leanh::lean_ctor_set(v___x_1829_, 0, v___x_1841_);
                    v___x_1844_ = v___x_1829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1841_);
                    v___x_1844_ = v_reuseFailAlloc_1870_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1845_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1845_, 0, v___x_1844_);
                leanh::lean_ctor_set(v___x_1845_, 1, v___x_1831_);
                v___x_1846_ = l_getCasesInfo_x3f___lam__0___closed__6;
                v___x_1847_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7___redArg(v___x_1845_, v___x_1846_);
                v_sz_1848_ = lean_array_size(v___x_1847_);
                leanh::lean_inc(v___x_1822_);
                v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00getCasesInfo_x3f_spec__8(v_val_1817_, v_a_1838_, v___x_1822_, v_sz_1848_, v___x_1836_, v___x_1847_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
                leanh::lean_dec(v_a_1838_);
                if leanh::lean_obj_tag(v___x_1849_) == 0 {
                    v_a_1850_ = leanh::lean_ctor_get(v___x_1849_, 0);
                    v_isSharedCheck_1861_ = (!leanh::lean_is_exclusive(v___x_1849_)) as u8;
                    if v_isSharedCheck_1861_ == 0 {
                        v___x_1852_ = v___x_1849_;
                        v_isShared_1853_ = v_isSharedCheck_1861_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1850_);
                        leanh::lean_dec(v___x_1849_);
                        v___x_1852_ = leanh::lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1861_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_1842_, 2);
                    leanh::lean_dec(v_val_1827_);
                    leanh::lean_del_object(v___x_1819_);
                    leanh::lean_dec(v_val_1817_);
                    leanh::lean_dec(v_declName_1797_);
                    v_a_1862_ = leanh::lean_ctor_get(v___x_1849_, 0);
                    v_isSharedCheck_1869_ = (!leanh::lean_is_exclusive(v___x_1849_)) as u8;
                    if v_isSharedCheck_1869_ == 0 {
                        v___x_1864_ = v___x_1849_;
                        v_isShared_1865_ = v_isSharedCheck_1869_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1862_);
                        leanh::lean_dec(v___x_1849_);
                        v___x_1864_ = leanh::lean_box(0);
                        v_isShared_1865_ = v_isSharedCheck_1869_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1854_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_1854_, 0, v_declName_1797_);
                leanh::lean_ctor_set(v___x_1854_, 1, v_val_1827_);
                leanh::lean_ctor_set(v___x_1854_, 2, v___x_1831_);
                leanh::lean_ctor_set(v___x_1854_, 3, v_val_1817_);
                leanh::lean_ctor_set(v___x_1854_, 4, v___x_1842_);
                leanh::lean_ctor_set(v___x_1854_, 5, v_a_1850_);
                if v_isShared_1820_ == 0 {
                    leanh::lean_ctor_set(v___x_1819_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1819_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1860_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1854_);
                    v___x_1856_ = v_reuseFailAlloc_1860_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1853_ == 0 {
                    leanh::lean_ctor_set(v___x_1852_, 0, v___x_1856_);
                    v___x_1858_ = v___x_1852_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1859_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
                    v___x_1858_ = v_reuseFailAlloc_1859_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1858_;
            }
            8 => {
                if v_isShared_1865_ == 0 {
                    v___x_1867_ = v___x_1864_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
                    v___x_1867_ = v_reuseFailAlloc_1868_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1867_;
            }
            10 => {
                if v_isShared_1882_ == 0 {
                    v___x_1884_ = v___x_1881_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1885_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
                    v___x_1884_ = v_reuseFailAlloc_1885_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1884_;
            }
            12 => {
                if v_isShared_1893_ == 0 {
                    v___x_1895_ = v___x_1892_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
                    v___x_1895_ = v_reuseFailAlloc_1896_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_getCasesInfo_x3f___lam__0___boxed(
    mut v_declName_1901_: *mut leanh::LeanObject,
    mut v_xs_1902_: *mut leanh::LeanObject,
    mut v_r_1903_: *mut leanh::LeanObject,
    mut v___y_1904_: *mut leanh::LeanObject,
    mut v___y_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
    mut v___y_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_getCasesInfo_x3f___lam__0(
        v_declName_1901_,
        v_xs_1902_,
        v_r_1903_,
        v___y_1904_,
        v___y_1905_,
        v___y_1906_,
        v___y_1907_,
    );
    leanh::lean_dec(v___y_1907_);
    leanh::lean_dec_ref(v___y_1906_);
    leanh::lean_dec(v___y_1905_);
    leanh::lean_dec_ref(v___y_1904_);
    leanh::lean_dec_ref(v_r_1903_);
    leanh::lean_dec_ref(v_xs_1902_);
    return v_res_1909_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1910_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__0);
    v___x_1912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1912_, 0, v___x_1911_);
    return v___x_1912_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1);
    v___x_1914_ = leanh::lean_unsigned_to_nat(0);
    v___x_1915_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1915_, 0, v___x_1914_);
    leanh::lean_ctor_set(v___x_1915_, 1, v___x_1914_);
    leanh::lean_ctor_set(v___x_1915_, 2, v___x_1914_);
    leanh::lean_ctor_set(v___x_1915_, 3, v___x_1914_);
    leanh::lean_ctor_set(v___x_1915_, 4, v___x_1913_);
    leanh::lean_ctor_set(v___x_1915_, 5, v___x_1913_);
    leanh::lean_ctor_set(v___x_1915_, 6, v___x_1913_);
    leanh::lean_ctor_set(v___x_1915_, 7, v___x_1913_);
    leanh::lean_ctor_set(v___x_1915_, 8, v___x_1913_);
    leanh::lean_ctor_set(v___x_1915_, 9, v___x_1913_);
    return v___x_1915_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = leanh::lean_unsigned_to_nat(32);
    v___x_1917_ = lean_mk_empty_array_with_capacity(v___x_1916_);
    v___x_1918_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1918_, 0, v___x_1917_);
    return v___x_1918_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1919_: usize = 0;
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = 5usize;
    v___x_1920_ = leanh::lean_unsigned_to_nat(0);
    v___x_1921_ = leanh::lean_unsigned_to_nat(32);
    v___x_1922_ = lean_mk_empty_array_with_capacity(v___x_1921_);
    v___x_1923_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__3);
    v___x_1924_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1924_, 0, v___x_1923_);
    leanh::lean_ctor_set(v___x_1924_, 1, v___x_1922_);
    leanh::lean_ctor_set(v___x_1924_, 2, v___x_1920_);
    leanh::lean_ctor_set(v___x_1924_, 3, v___x_1920_);
    leanh::lean_ctor_set_usize(v___x_1924_, 4, v___x_1919_);
    return v___x_1924_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = leanh::lean_box(1);
    v___x_1926_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4);
    v___x_1927_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__1);
    v___x_1928_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1928_, 0, v___x_1927_);
    leanh::lean_ctor_set(v___x_1928_, 1, v___x_1926_);
    leanh::lean_ctor_set(v___x_1928_, 2, v___x_1925_);
    return v___x_1928_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__6;
    v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
    return v___x_1931_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1933_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__8;
    v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1936_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__10;
    v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__12;
    v___x_1940_ = l_Lean_stringToMessageData(v___x_1939_);
    return v___x_1940_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__14;
    v___x_1943_ = l_Lean_stringToMessageData(v___x_1942_);
    return v___x_1943_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__16;
    v___x_1946_ = l_Lean_stringToMessageData(v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__18;
    v___x_1949_ = l_Lean_stringToMessageData(v___x_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(
    mut v_msg_1950_: *mut leanh::LeanObject,
    mut v_declHint_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u8 = 0;
    let mut v_isExporting_1957_: u8 = 0;
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: u8 = 0;
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1954_ = lean_st_ref_get(v___y_1952_);
                v_env_1955_ = leanh::lean_ctor_get(v___x_1954_, 0);
                leanh::lean_inc_ref(v_env_1955_);
                leanh::lean_dec(v___x_1954_);
                v___x_1956_ = l_Lean_Name_isAnonymous(v_declHint_1951_);
                if v___x_1956_ == 0 {
                    v_isExporting_1957_ = leanh::lean_ctor_get_uint8(
                        v_env_1955_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1957_ == 0 {
                        leanh::lean_dec_ref(v_env_1955_);
                        leanh::lean_dec(v_declHint_1951_);
                        v___x_1958_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1958_, 0, v_msg_1950_);
                        return v___x_1958_;
                    } else {
                        leanh::lean_inc_ref(v_env_1955_);
                        v___x_1959_ = l_Lean_Environment_setExporting(v_env_1955_, v___x_1956_);
                        leanh::lean_inc(v_declHint_1951_);
                        leanh::lean_inc_ref(v___x_1959_);
                        v___x_1960_ = l_Lean_Environment_contains(
                            v___x_1959_,
                            v_declHint_1951_,
                            v_isExporting_1957_,
                        );
                        if v___x_1960_ == 0 {
                            leanh::lean_dec_ref(v___x_1959_);
                            leanh::lean_dec_ref(v_env_1955_);
                            leanh::lean_dec(v_declHint_1951_);
                            v___x_1961_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1961_, 0, v_msg_1950_);
                            return v___x_1961_;
                        } else {
                            v___x_1962_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2);
                            v___x_1963_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5);
                            v___x_1964_ = l_Lean_Options_empty;
                            v___x_1965_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1965_, 0, v___x_1959_);
                            leanh::lean_ctor_set(v___x_1965_, 1, v___x_1962_);
                            leanh::lean_ctor_set(v___x_1965_, 2, v___x_1963_);
                            leanh::lean_ctor_set(v___x_1965_, 3, v___x_1964_);
                            leanh::lean_inc(v_declHint_1951_);
                            v___x_1966_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1951_, v___x_1956_);
                            v_c_1967_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1967_, 0, v___x_1965_);
                            leanh::lean_ctor_set(v_c_1967_, 1, v___x_1966_);
                            v___x_1968_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1955_,
                                v_declHint_1951_,
                            );
                            if leanh::lean_obj_tag(v___x_1968_) == 0 {
                                leanh::lean_dec_ref(v_env_1955_);
                                leanh::lean_dec(v_declHint_1951_);
                                v___x_1969_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7);
                                v___x_1970_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1970_, 0, v___x_1969_);
                                leanh::lean_ctor_set(v___x_1970_, 1, v_c_1967_);
                                v___x_1971_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__9);
                                v___x_1972_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1972_, 0, v___x_1970_);
                                leanh::lean_ctor_set(v___x_1972_, 1, v___x_1971_);
                                v___x_1973_ = l_Lean_MessageData_note(v___x_1972_);
                                v___x_1974_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1974_, 0, v_msg_1950_);
                                leanh::lean_ctor_set(v___x_1974_, 1, v___x_1973_);
                                v___x_1975_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1975_, 0, v___x_1974_);
                                return v___x_1975_;
                            } else {
                                v_val_1976_ = leanh::lean_ctor_get(v___x_1968_, 0);
                                v_isSharedCheck_2011_ =
                                    (!leanh::lean_is_exclusive(v___x_1968_)) as u8;
                                if v_isSharedCheck_2011_ == 0 {
                                    v___x_1978_ = v___x_1968_;
                                    v_isShared_1979_ = v_isSharedCheck_2011_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1976_);
                                    leanh::lean_dec(v___x_1968_);
                                    v___x_1978_ = leanh::lean_box(0);
                                    v_isShared_1979_ = v_isSharedCheck_2011_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1955_);
                    leanh::lean_dec(v_declHint_1951_);
                    v___x_2012_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2012_, 0, v_msg_1950_);
                    return v___x_2012_;
                }
            }
            1 => {
                v___x_1980_ = leanh::lean_box(0);
                v___x_1981_ = l_Lean_Environment_header(v_env_1955_);
                leanh::lean_dec_ref(v_env_1955_);
                v___x_1982_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1981_);
                v_mod_1983_ = lean_array_get(v___x_1980_, v___x_1982_, v_val_1976_);
                leanh::lean_dec(v_val_1976_);
                leanh::lean_dec_ref(v___x_1982_);
                v___x_1984_ = l_Lean_isPrivateName(v_declHint_1951_);
                leanh::lean_dec(v_declHint_1951_);
                if v___x_1984_ == 0 {
                    v___x_1985_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__11);
                    v___x_1986_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1986_, 0, v___x_1985_);
                    leanh::lean_ctor_set(v___x_1986_, 1, v_c_1967_);
                    v___x_1987_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__13);
                    v___x_1988_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1988_, 0, v___x_1986_);
                    leanh::lean_ctor_set(v___x_1988_, 1, v___x_1987_);
                    v___x_1989_ = l_Lean_MessageData_ofName(v_mod_1983_);
                    v___x_1990_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1990_, 0, v___x_1988_);
                    leanh::lean_ctor_set(v___x_1990_, 1, v___x_1989_);
                    v___x_1991_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__15);
                    v___x_1992_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1992_, 0, v___x_1990_);
                    leanh::lean_ctor_set(v___x_1992_, 1, v___x_1991_);
                    v___x_1993_ = l_Lean_MessageData_note(v___x_1992_);
                    v___x_1994_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1994_, 0, v_msg_1950_);
                    leanh::lean_ctor_set(v___x_1994_, 1, v___x_1993_);
                    if v_isShared_1979_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1978_, 0);
                        leanh::lean_ctor_set(v___x_1978_, 0, v___x_1994_);
                        v___x_1996_ = v___x_1978_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
                        v___x_1996_ = v_reuseFailAlloc_1997_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1998_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__7);
                    v___x_1999_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1999_, 0, v___x_1998_);
                    leanh::lean_ctor_set(v___x_1999_, 1, v_c_1967_);
                    v___x_2000_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__17);
                    v___x_2001_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2001_, 0, v___x_1999_);
                    leanh::lean_ctor_set(v___x_2001_, 1, v___x_2000_);
                    v___x_2002_ = l_Lean_MessageData_ofName(v_mod_1983_);
                    v___x_2003_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2003_, 0, v___x_2001_);
                    leanh::lean_ctor_set(v___x_2003_, 1, v___x_2002_);
                    v___x_2004_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__19);
                    v___x_2005_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2005_, 0, v___x_2003_);
                    leanh::lean_ctor_set(v___x_2005_, 1, v___x_2004_);
                    v___x_2006_ = l_Lean_MessageData_note(v___x_2005_);
                    v___x_2007_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2007_, 0, v_msg_1950_);
                    leanh::lean_ctor_set(v___x_2007_, 1, v___x_2006_);
                    if v_isShared_1979_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1978_, 0);
                        leanh::lean_ctor_set(v___x_1978_, 0, v___x_2007_);
                        v___x_2009_ = v___x_1978_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
                        v___x_2009_ = v_reuseFailAlloc_2010_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1996_;
            }
            3 => {
                return v___x_2009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___boxed(
    mut v_msg_2013_: *mut leanh::LeanObject,
    mut v_declHint_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2017_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(v_msg_2013_, v_declHint_2014_, v___y_2015_);
    leanh::lean_dec(v___y_2015_);
    return v_res_2017_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(
    mut v_msg_2018_: *mut leanh::LeanObject,
    mut v_declHint_2019_: *mut leanh::LeanObject,
    mut v___y_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(v_msg_2018_, v_declHint_2019_, v___y_2021_);
                v_a_2024_ = leanh::lean_ctor_get(v___x_2023_, 0);
                v_isSharedCheck_2033_ = (!leanh::lean_is_exclusive(v___x_2023_)) as u8;
                if v_isSharedCheck_2033_ == 0 {
                    v___x_2026_ = v___x_2023_;
                    v_isShared_2027_ = v_isSharedCheck_2033_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2024_);
                    leanh::lean_dec(v___x_2023_);
                    v___x_2026_ = leanh::lean_box(0);
                    v_isShared_2027_ = v_isSharedCheck_2033_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2028_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2029_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2029_, 0, v___x_2028_);
                leanh::lean_ctor_set(v___x_2029_, 1, v_a_2024_);
                if v_isShared_2027_ == 0 {
                    leanh::lean_ctor_set(v___x_2026_, 0, v___x_2029_);
                    v___x_2031_ = v___x_2026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
                    v___x_2031_ = v_reuseFailAlloc_2032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15___boxed(
    mut v_msg_2034_: *mut leanh::LeanObject,
    mut v_declHint_2035_: *mut leanh::LeanObject,
    mut v___y_2036_: *mut leanh::LeanObject,
    mut v___y_2037_: *mut leanh::LeanObject,
    mut v___y_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(v_msg_2034_, v_declHint_2035_, v___y_2036_, v___y_2037_);
    leanh::lean_dec(v___y_2037_);
    leanh::lean_dec_ref(v___y_2036_);
    return v_res_2039_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(
    mut v_msgData_2040_: *mut leanh::LeanObject,
    mut v___y_2041_: *mut leanh::LeanObject,
    mut v___y_2042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = lean_st_ref_get(v___y_2042_);
    v_env_2045_ = leanh::lean_ctor_get(v___x_2044_, 0);
    leanh::lean_inc_ref(v_env_2045_);
    leanh::lean_dec(v___x_2044_);
    v_options_2046_ = leanh::lean_ctor_get(v___y_2041_, 2);
    v___x_2047_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__2);
    v___x_2048_ = leanh::lean_unsigned_to_nat(32);
    v___x_2049_ = lean_mk_empty_array_with_capacity(v___x_2048_);
    leanh::lean_dec_ref(v___x_2049_);
    v___x_2050_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__5);
    leanh::lean_inc_ref(v_options_2046_);
    v___x_2051_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2051_, 0, v_env_2045_);
    leanh::lean_ctor_set(v___x_2051_, 1, v___x_2047_);
    leanh::lean_ctor_set(v___x_2051_, 2, v___x_2050_);
    leanh::lean_ctor_set(v___x_2051_, 3, v_options_2046_);
    v___x_2052_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2052_, 0, v___x_2051_);
    leanh::lean_ctor_set(v___x_2052_, 1, v_msgData_2040_);
    v___x_2053_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2053_, 0, v___x_2052_);
    return v___x_2053_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20___boxed(
    mut v_msgData_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2058_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(v_msgData_2054_, v___y_2055_, v___y_2056_);
    leanh::lean_dec(v___y_2056_);
    leanh::lean_dec_ref(v___y_2055_);
    return v_res_2058_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(
    mut v_msg_2059_: *mut leanh::LeanObject,
    mut v___y_2060_: *mut leanh::LeanObject,
    mut v___y_2061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2063_ = leanh::lean_ctor_get(v___y_2060_, 5);
                v___x_2064_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19_spec__20(v_msg_2059_, v___y_2060_, v___y_2061_);
                v_a_2065_ = leanh::lean_ctor_get(v___x_2064_, 0);
                v_isSharedCheck_2073_ = (!leanh::lean_is_exclusive(v___x_2064_)) as u8;
                if v_isSharedCheck_2073_ == 0 {
                    v___x_2067_ = v___x_2064_;
                    v_isShared_2068_ = v_isSharedCheck_2073_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2065_);
                    leanh::lean_dec(v___x_2064_);
                    v___x_2067_ = leanh::lean_box(0);
                    v_isShared_2068_ = v_isSharedCheck_2073_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2063_);
                v___x_2069_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2069_, 0, v_ref_2063_);
                leanh::lean_ctor_set(v___x_2069_, 1, v_a_2065_);
                if v_isShared_2068_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2067_, 1);
                    leanh::lean_ctor_set(v___x_2067_, 0, v___x_2069_);
                    v___x_2071_ = v___x_2067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2072_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
                    v___x_2071_ = v_reuseFailAlloc_2072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg___boxed(
    mut v_msg_2074_: *mut leanh::LeanObject,
    mut v___y_2075_: *mut leanh::LeanObject,
    mut v___y_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2078_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(v_msg_2074_, v___y_2075_, v___y_2076_);
    leanh::lean_dec(v___y_2076_);
    leanh::lean_dec_ref(v___y_2075_);
    return v_res_2078_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(
    mut v_ref_2079_: *mut leanh::LeanObject,
    mut v_msg_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2096_: u8 = 0;
    let mut v_cancelTk_x3f_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2098_: u8 = 0;
    let mut v_inheritedTraceOptions_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2084_ = leanh::lean_ctor_get(v___y_2081_, 0);
    v_fileMap_2085_ = leanh::lean_ctor_get(v___y_2081_, 1);
    v_options_2086_ = leanh::lean_ctor_get(v___y_2081_, 2);
    v_currRecDepth_2087_ = leanh::lean_ctor_get(v___y_2081_, 3);
    v_maxRecDepth_2088_ = leanh::lean_ctor_get(v___y_2081_, 4);
    v_ref_2089_ = leanh::lean_ctor_get(v___y_2081_, 5);
    v_currNamespace_2090_ = leanh::lean_ctor_get(v___y_2081_, 6);
    v_openDecls_2091_ = leanh::lean_ctor_get(v___y_2081_, 7);
    v_initHeartbeats_2092_ = leanh::lean_ctor_get(v___y_2081_, 8);
    v_maxHeartbeats_2093_ = leanh::lean_ctor_get(v___y_2081_, 9);
    v_quotContext_2094_ = leanh::lean_ctor_get(v___y_2081_, 10);
    v_currMacroScope_2095_ = leanh::lean_ctor_get(v___y_2081_, 11);
    v_diag_2096_ = leanh::lean_ctor_get_uint8(
        v___y_2081_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2097_ = leanh::lean_ctor_get(v___y_2081_, 12);
    v_suppressElabErrors_2098_ = leanh::lean_ctor_get_uint8(
        v___y_2081_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2099_ = leanh::lean_ctor_get(v___y_2081_, 13);
    v_ref_2100_ = l_Lean_replaceRef(v_ref_2079_, v_ref_2089_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_2099_);
    leanh::lean_inc(v_cancelTk_x3f_2097_);
    leanh::lean_inc(v_currMacroScope_2095_);
    leanh::lean_inc(v_quotContext_2094_);
    leanh::lean_inc(v_maxHeartbeats_2093_);
    leanh::lean_inc(v_initHeartbeats_2092_);
    leanh::lean_inc(v_openDecls_2091_);
    leanh::lean_inc(v_currNamespace_2090_);
    leanh::lean_inc(v_maxRecDepth_2088_);
    leanh::lean_inc(v_currRecDepth_2087_);
    leanh::lean_inc_ref(v_options_2086_);
    leanh::lean_inc_ref(v_fileMap_2085_);
    leanh::lean_inc_ref(v_fileName_2084_);
    v___x_2101_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_2101_, 0, v_fileName_2084_);
    leanh::lean_ctor_set(v___x_2101_, 1, v_fileMap_2085_);
    leanh::lean_ctor_set(v___x_2101_, 2, v_options_2086_);
    leanh::lean_ctor_set(v___x_2101_, 3, v_currRecDepth_2087_);
    leanh::lean_ctor_set(v___x_2101_, 4, v_maxRecDepth_2088_);
    leanh::lean_ctor_set(v___x_2101_, 5, v_ref_2100_);
    leanh::lean_ctor_set(v___x_2101_, 6, v_currNamespace_2090_);
    leanh::lean_ctor_set(v___x_2101_, 7, v_openDecls_2091_);
    leanh::lean_ctor_set(v___x_2101_, 8, v_initHeartbeats_2092_);
    leanh::lean_ctor_set(v___x_2101_, 9, v_maxHeartbeats_2093_);
    leanh::lean_ctor_set(v___x_2101_, 10, v_quotContext_2094_);
    leanh::lean_ctor_set(v___x_2101_, 11, v_currMacroScope_2095_);
    leanh::lean_ctor_set(v___x_2101_, 12, v_cancelTk_x3f_2097_);
    leanh::lean_ctor_set(v___x_2101_, 13, v_inheritedTraceOptions_2099_);
    leanh::lean_ctor_set_uint8(
        v___x_2101_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_2096_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2101_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2098_,
    );
    v___x_2102_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(v_msg_2080_, v___x_2101_, v___y_2082_);
    leanh::lean_dec_ref_known(v___x_2101_, 14);
    return v___x_2102_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg___boxed(
    mut v_ref_2103_: *mut leanh::LeanObject,
    mut v_msg_2104_: *mut leanh::LeanObject,
    mut v___y_2105_: *mut leanh::LeanObject,
    mut v___y_2106_: *mut leanh::LeanObject,
    mut v___y_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(v_ref_2103_, v_msg_2104_, v___y_2105_, v___y_2106_);
    leanh::lean_dec(v___y_2106_);
    leanh::lean_dec_ref(v___y_2105_);
    leanh::lean_dec(v_ref_2103_);
    return v_res_2108_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(
    mut v_ref_2109_: *mut leanh::LeanObject,
    mut v_msg_2110_: *mut leanh::LeanObject,
    mut v_declHint_2111_: *mut leanh::LeanObject,
    mut v___y_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15(v_msg_2110_, v_declHint_2111_, v___y_2112_, v___y_2113_);
    v_a_2116_ = leanh::lean_ctor_get(v___x_2115_, 0);
    leanh::lean_inc(v_a_2116_);
    leanh::lean_dec_ref(v___x_2115_);
    v___x_2117_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(v_ref_2109_, v_a_2116_, v___y_2112_, v___y_2113_);
    return v___x_2117_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg___boxed(
    mut v_ref_2118_: *mut leanh::LeanObject,
    mut v_msg_2119_: *mut leanh::LeanObject,
    mut v_declHint_2120_: *mut leanh::LeanObject,
    mut v___y_2121_: *mut leanh::LeanObject,
    mut v___y_2122_: *mut leanh::LeanObject,
    mut v___y_2123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2124_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2118_, v_msg_2119_, v_declHint_2120_, v___y_2121_, v___y_2122_);
    leanh::lean_dec(v___y_2122_);
    leanh::lean_dec_ref(v___y_2121_);
    leanh::lean_dec(v_ref_2118_);
    return v_res_2124_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__0;
    v___x_2127_ = l_Lean_stringToMessageData(v___x_2126_);
    return v___x_2127_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(
    mut v_ref_2128_: *mut leanh::LeanObject,
    mut v_constName_2129_: *mut leanh::LeanObject,
    mut v___y_2130_: *mut leanh::LeanObject,
    mut v___y_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2133_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___closed__1);
    v___x_2134_ = 0;
    leanh::lean_inc(v_constName_2129_);
    v___x_2135_ = l_Lean_MessageData_ofConstName(v_constName_2129_, v___x_2134_);
    v___x_2136_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2136_, 0, v___x_2133_);
    leanh::lean_ctor_set(v___x_2136_, 1, v___x_2135_);
    v___x_2137_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1_once
        ),
        _init_l_Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4___closed__1,
    );
    v___x_2138_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2138_, 0, v___x_2136_);
    leanh::lean_ctor_set(v___x_2138_, 1, v___x_2137_);
    v___x_2139_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2128_, v___x_2138_, v_constName_2129_, v___y_2130_, v___y_2131_);
    return v___x_2139_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg___boxed(
    mut v_ref_2140_: *mut leanh::LeanObject,
    mut v_constName_2141_: *mut leanh::LeanObject,
    mut v___y_2142_: *mut leanh::LeanObject,
    mut v___y_2143_: *mut leanh::LeanObject,
    mut v___y_2144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2145_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(v_ref_2140_, v_constName_2141_, v___y_2142_, v___y_2143_);
    leanh::lean_dec(v___y_2143_);
    leanh::lean_dec_ref(v___y_2142_);
    leanh::lean_dec(v_ref_2140_);
    return v_res_2145_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg(
    mut v_constName_2146_: *mut leanh::LeanObject,
    mut v___y_2147_: *mut leanh::LeanObject,
    mut v___y_2148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2150_ = leanh::lean_ctor_get(v___y_2147_, 5);
    v___x_2151_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(v_ref_2150_, v_constName_2146_, v___y_2147_, v___y_2148_);
    return v___x_2151_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_2152_: *mut leanh::LeanObject,
    mut v___y_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
    mut v___y_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg(v_constName_2152_, v___y_2153_, v___y_2154_);
    leanh::lean_dec(v___y_2154_);
    leanh::lean_dec_ref(v___y_2153_);
    return v_res_2156_;
}
pub unsafe fn l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0(
    mut v_constName_2157_: *mut leanh::LeanObject,
    mut v___y_2158_: *mut leanh::LeanObject,
    mut v___y_2159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2169_: u8 = 0;
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2161_ = lean_st_ref_get(v___y_2159_);
                v_env_2162_ = leanh::lean_ctor_get(v___x_2161_, 0);
                leanh::lean_inc_ref(v_env_2162_);
                leanh::lean_dec(v___x_2161_);
                v___x_2163_ = 0;
                leanh::lean_inc(v_constName_2157_);
                v___x_2164_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_2162_,
                    v_constName_2157_,
                    v___x_2163_,
                );
                if leanh::lean_obj_tag(v___x_2164_) == 0 {
                    v___x_2165_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg(v_constName_2157_, v___y_2158_, v___y_2159_);
                    return v___x_2165_;
                } else {
                    leanh::lean_dec(v_constName_2157_);
                    v_val_2166_ = leanh::lean_ctor_get(v___x_2164_, 0);
                    v_isSharedCheck_2173_ = (!leanh::lean_is_exclusive(v___x_2164_)) as u8;
                    if v_isSharedCheck_2173_ == 0 {
                        v___x_2168_ = v___x_2164_;
                        v_isShared_2169_ = v_isSharedCheck_2173_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2166_);
                        leanh::lean_dec(v___x_2164_);
                        v___x_2168_ = leanh::lean_box(0);
                        v_isShared_2169_ = v_isSharedCheck_2173_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2169_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2168_, 0);
                    v___x_2171_ = v___x_2168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_val_2166_);
                    v___x_2171_ = v_reuseFailAlloc_2172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0___boxed(
    mut v_constName_2174_: *mut leanh::LeanObject,
    mut v___y_2175_: *mut leanh::LeanObject,
    mut v___y_2176_: *mut leanh::LeanObject,
    mut v___y_2177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2178_ = l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0(
        v_constName_2174_,
        v___y_2175_,
        v___y_2176_,
    );
    leanh::lean_dec(v___y_2176_);
    leanh::lean_dec_ref(v___y_2175_);
    return v_res_2178_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2179_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2179_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__0),
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__0_once),
        _init_l_getCasesInfo_x3f___closed__0,
    );
    v___x_2181_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2181_, 0, v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = leanh::lean_box(1);
    v___x_2183_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4);
    v___x_2184_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__1),
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__1_once),
        _init_l_getCasesInfo_x3f___closed__1,
    );
    v___x_2185_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2185_, 0, v___x_2184_);
    leanh::lean_ctor_set(v___x_2185_, 1, v___x_2183_);
    leanh::lean_ctor_set(v___x_2185_, 2, v___x_2182_);
    return v___x_2185_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__1),
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__1_once),
        _init_l_getCasesInfo_x3f___closed__1,
    );
    v___x_2189_ = leanh::lean_unsigned_to_nat(0);
    v___x_2190_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2190_, 0, v___x_2189_);
    leanh::lean_ctor_set(v___x_2190_, 1, v___x_2189_);
    leanh::lean_ctor_set(v___x_2190_, 2, v___x_2189_);
    leanh::lean_ctor_set(v___x_2190_, 3, v___x_2189_);
    leanh::lean_ctor_set(v___x_2190_, 4, v___x_2188_);
    leanh::lean_ctor_set(v___x_2190_, 5, v___x_2188_);
    leanh::lean_ctor_set(v___x_2190_, 6, v___x_2188_);
    leanh::lean_ctor_set(v___x_2190_, 7, v___x_2188_);
    leanh::lean_ctor_set(v___x_2190_, 8, v___x_2188_);
    leanh::lean_ctor_set(v___x_2190_, 9, v___x_2188_);
    return v___x_2190_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__1),
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__1_once),
        _init_l_getCasesInfo_x3f___closed__1,
    );
    v___x_2192_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2192_, 0, v___x_2191_);
    leanh::lean_ctor_set(v___x_2192_, 1, v___x_2191_);
    leanh::lean_ctor_set(v___x_2192_, 2, v___x_2191_);
    leanh::lean_ctor_set(v___x_2192_, 3, v___x_2191_);
    leanh::lean_ctor_set(v___x_2192_, 4, v___x_2191_);
    leanh::lean_ctor_set(v___x_2192_, 5, v___x_2191_);
    return v___x_2192_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2193_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__1),
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__1_once),
        _init_l_getCasesInfo_x3f___closed__1,
    );
    v___x_2194_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2194_, 0, v___x_2193_);
    leanh::lean_ctor_set(v___x_2194_, 1, v___x_2193_);
    leanh::lean_ctor_set(v___x_2194_, 2, v___x_2193_);
    leanh::lean_ctor_set(v___x_2194_, 3, v___x_2193_);
    leanh::lean_ctor_set(v___x_2194_, 4, v___x_2193_);
    return v___x_2194_;
}
pub unsafe fn _init_l_getCasesInfo_x3f___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__6),
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__6_once),
        _init_l_getCasesInfo_x3f___closed__6,
    );
    v___x_2196_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg___closed__4);
    v___x_2197_ = leanh::lean_box(1);
    v___x_2198_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__5),
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__5_once),
        _init_l_getCasesInfo_x3f___closed__5,
    );
    v___x_2199_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__4),
        core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__4_once),
        _init_l_getCasesInfo_x3f___closed__4,
    );
    v___x_2200_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2200_, 0, v___x_2199_);
    leanh::lean_ctor_set(v___x_2200_, 1, v___x_2198_);
    leanh::lean_ctor_set(v___x_2200_, 2, v___x_2197_);
    leanh::lean_ctor_set(v___x_2200_, 3, v___x_2196_);
    leanh::lean_ctor_set(v___x_2200_, 4, v___x_2195_);
    return v___x_2200_;
}
pub unsafe fn l_getCasesInfo_x3f(
    mut v_declName_2201_: *mut leanh::LeanObject,
    mut v_a_2202_: *mut leanh::LeanObject,
    mut v_a_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: u8 = 0;
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: u8 = 0;
    let mut v___x_2215_: u8 = 0;
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: u64 = 0;
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_a_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2242_: u8 = 0;
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2205_ = lean_st_ref_get(v_a_2203_);
                v_env_2206_ = leanh::lean_ctor_get(v___x_2205_, 0);
                leanh::lean_inc_ref(v_env_2206_);
                leanh::lean_dec(v___x_2205_);
                leanh::lean_inc(v_declName_2201_);
                v___x_2207_ = l_Lean_isCasesOnLike(v_env_2206_, v_declName_2201_);
                if v___x_2207_ == 0 {
                    leanh::lean_dec(v_declName_2201_);
                    v___x_2208_ = leanh::lean_box(0);
                    v___x_2209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2209_, 0, v___x_2208_);
                    return v___x_2209_;
                } else {
                    leanh::lean_inc(v_declName_2201_);
                    v___x_2210_ = l_Lean_getConstVal___at___00getCasesInfo_x3f_spec__0(
                        v_declName_2201_,
                        v_a_2202_,
                        v_a_2203_,
                    );
                    if leanh::lean_obj_tag(v___x_2210_) == 0 {
                        v_a_2211_ = leanh::lean_ctor_get(v___x_2210_, 0);
                        leanh::lean_inc(v_a_2211_);
                        leanh::lean_dec_ref_known(v___x_2210_, 1);
                        v___x_2212_ = 0;
                        v___x_2213_ = 1;
                        v___x_2214_ = 0;
                        v___x_2215_ = 2;
                        v___x_2216_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 0 as u32, v___x_2212_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 1 as u32, v___x_2212_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 2 as u32, v___x_2212_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 3 as u32, v___x_2212_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 4 as u32, v___x_2212_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 5 as u32, v___x_2207_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 6 as u32, v___x_2207_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 7 as u32, v___x_2212_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 8 as u32, v___x_2207_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 9 as u32, v___x_2213_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 10 as u32, v___x_2214_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 11 as u32, v___x_2207_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 12 as u32, v___x_2207_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 13 as u32, v___x_2207_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 14 as u32, v___x_2215_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 15 as u32, v___x_2207_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 16 as u32, v___x_2207_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 17 as u32, v___x_2207_);
                        leanh::lean_ctor_set_uint8(v___x_2216_, 18 as u32, v___x_2207_);
                        v___x_2217_ =
                            l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2216_);
                        v___x_2218_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                        leanh::lean_ctor_set(v___x_2218_, 0, v___x_2216_);
                        leanh::lean_ctor_set_uint64(
                            v___x_2218_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_2217_,
                        );
                        v___x_2219_ = leanh::lean_box(1);
                        v___x_2220_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2221_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__2),
                            core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__2_once),
                            _init_l_getCasesInfo_x3f___closed__2,
                        );
                        v___x_2222_ = l_getCasesInfo_x3f___closed__3;
                        v___x_2223_ = leanh::lean_box(0);
                        v___x_2224_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                        leanh::lean_ctor_set(v___x_2224_, 0, v___x_2218_);
                        leanh::lean_ctor_set(v___x_2224_, 1, v___x_2219_);
                        leanh::lean_ctor_set(v___x_2224_, 2, v___x_2221_);
                        leanh::lean_ctor_set(v___x_2224_, 3, v___x_2222_);
                        leanh::lean_ctor_set(v___x_2224_, 4, v___x_2223_);
                        leanh::lean_ctor_set(v___x_2224_, 5, v___x_2220_);
                        leanh::lean_ctor_set(v___x_2224_, 6, v___x_2223_);
                        leanh::lean_ctor_set_uint8(
                            v___x_2224_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                            v___x_2212_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_2224_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                            v___x_2212_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_2224_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                            v___x_2212_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_2224_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                            v___x_2207_,
                        );
                        v___x_2225_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__7),
                            core::ptr::addr_of_mut!(l_getCasesInfo_x3f___closed__7_once),
                            _init_l_getCasesInfo_x3f___closed__7,
                        );
                        v___x_2226_ = lean_st_mk_ref(v___x_2225_);
                        v_type_2227_ = leanh::lean_ctor_get(v_a_2211_, 2);
                        leanh::lean_inc_ref(v_type_2227_);
                        leanh::lean_dec(v_a_2211_);
                        v___f_2228_ = leanh::lean_alloc_closure(
                            l_getCasesInfo_x3f___lam__0___boxed as *mut core::ffi::c_void,
                            8,
                            1,
                        );
                        leanh::lean_closure_set(v___f_2228_, 0, v_declName_2201_);
                        v___x_2229_ =
                            l_Lean_Meta_forallTelescope___at___00getCasesInfo_x3f_spec__6___redArg(
                                v_type_2227_,
                                v___f_2228_,
                                v___x_2212_,
                                v___x_2224_,
                                v___x_2226_,
                                v_a_2202_,
                                v_a_2203_,
                            );
                        leanh::lean_dec_ref_known(v___x_2224_, 7);
                        if leanh::lean_obj_tag(v___x_2229_) == 0 {
                            v_a_2230_ = leanh::lean_ctor_get(v___x_2229_, 0);
                            v_isSharedCheck_2238_ =
                                (!leanh::lean_is_exclusive(v___x_2229_)) as u8;
                            if v_isSharedCheck_2238_ == 0 {
                                v___x_2232_ = v___x_2229_;
                                v_isShared_2233_ = v_isSharedCheck_2238_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2230_);
                                leanh::lean_dec(v___x_2229_);
                                v___x_2232_ = leanh::lean_box(0);
                                v_isShared_2233_ = v_isSharedCheck_2238_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_2226_);
                            return v___x_2229_;
                        }
                    } else {
                        leanh::lean_dec(v_declName_2201_);
                        v_a_2239_ = leanh::lean_ctor_get(v___x_2210_, 0);
                        v_isSharedCheck_2246_ =
                            (!leanh::lean_is_exclusive(v___x_2210_)) as u8;
                        if v_isSharedCheck_2246_ == 0 {
                            v___x_2241_ = v___x_2210_;
                            v_isShared_2242_ = v_isSharedCheck_2246_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2239_);
                            leanh::lean_dec(v___x_2210_);
                            v___x_2241_ = leanh::lean_box(0);
                            v_isShared_2242_ = v_isSharedCheck_2246_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2234_ = lean_st_ref_get(v___x_2226_);
                leanh::lean_dec(v___x_2226_);
                leanh::lean_dec(v___x_2234_);
                if v_isShared_2233_ == 0 {
                    v___x_2236_ = v___x_2232_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2230_);
                    v___x_2236_ = v_reuseFailAlloc_2237_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2236_;
            }
            3 => {
                if v_isShared_2242_ == 0 {
                    v___x_2244_ = v___x_2241_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2245_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
                    v___x_2244_ = v_reuseFailAlloc_2245_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_getCasesInfo_x3f___boxed(
    mut v_declName_2247_: *mut leanh::LeanObject,
    mut v_a_2248_: *mut leanh::LeanObject,
    mut v_a_2249_: *mut leanh::LeanObject,
    mut v_a_2250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2251_ = l_getCasesInfo_x3f(v_declName_2247_, v_a_2248_, v_a_2249_);
    leanh::lean_dec(v_a_2249_);
    leanh::lean_dec_ref(v_a_2248_);
    return v_res_2251_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7(
    mut v_inst_2252_: *mut leanh::LeanObject,
    mut v_R_2253_: *mut leanh::LeanObject,
    mut v_a_2254_: *mut leanh::LeanObject,
    mut v_b_2255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2256_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00getCasesInfo_x3f_spec__7___redArg(v_a_2254_, v_b_2255_);
    return v___x_2256_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0(
    mut v_00_u03b1_2257_: *mut leanh::LeanObject,
    mut v_constName_2258_: *mut leanh::LeanObject,
    mut v___y_2259_: *mut leanh::LeanObject,
    mut v___y_2260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2262_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___redArg(v_constName_2258_, v___y_2259_, v___y_2260_);
    return v___x_2262_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_2263_: *mut leanh::LeanObject,
    mut v_constName_2264_: *mut leanh::LeanObject,
    mut v___y_2265_: *mut leanh::LeanObject,
    mut v___y_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0(v_00_u03b1_2263_, v_constName_2264_, v___y_2265_, v___y_2266_);
    leanh::lean_dec(v___y_2266_);
    leanh::lean_dec_ref(v___y_2265_);
    return v_res_2268_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6(
    mut v_00_u03b1_2269_: *mut leanh::LeanObject,
    mut v_msg_2270_: *mut leanh::LeanObject,
    mut v___y_2271_: *mut leanh::LeanObject,
    mut v___y_2272_: *mut leanh::LeanObject,
    mut v___y_2273_: *mut leanh::LeanObject,
    mut v___y_2274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___redArg(v_msg_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
    return v___x_2276_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6___boxed(
    mut v_00_u03b1_2277_: *mut leanh::LeanObject,
    mut v_msg_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
    mut v___y_2280_: *mut leanh::LeanObject,
    mut v___y_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
    mut v___y_2283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2284_ =
        l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00getCasesInfo_x3f_spec__4_spec__6(
            v_00_u03b1_2277_,
            v_msg_2278_,
            v___y_2279_,
            v___y_2280_,
            v___y_2281_,
            v___y_2282_,
        );
    leanh::lean_dec(v___y_2282_);
    leanh::lean_dec_ref(v___y_2281_);
    leanh::lean_dec(v___y_2280_);
    leanh::lean_dec_ref(v___y_2279_);
    return v_res_2284_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4(
    mut v_00_u03b1_2285_: *mut leanh::LeanObject,
    mut v_ref_2286_: *mut leanh::LeanObject,
    mut v_constName_2287_: *mut leanh::LeanObject,
    mut v___y_2288_: *mut leanh::LeanObject,
    mut v___y_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2291_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___redArg(v_ref_2286_, v_constName_2287_, v___y_2288_, v___y_2289_);
    return v___x_2291_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b1_2292_: *mut leanh::LeanObject,
    mut v_ref_2293_: *mut leanh::LeanObject,
    mut v_constName_2294_: *mut leanh::LeanObject,
    mut v___y_2295_: *mut leanh::LeanObject,
    mut v___y_2296_: *mut leanh::LeanObject,
    mut v___y_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2298_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4(v_00_u03b1_2292_, v_ref_2293_, v_constName_2294_, v___y_2295_, v___y_2296_);
    leanh::lean_dec(v___y_2296_);
    leanh::lean_dec_ref(v___y_2295_);
    leanh::lean_dec(v_ref_2293_);
    return v_res_2298_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11(
    mut v_00_u03b1_2299_: *mut leanh::LeanObject,
    mut v_ref_2300_: *mut leanh::LeanObject,
    mut v_msg_2301_: *mut leanh::LeanObject,
    mut v_declHint_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
    mut v___y_2304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2306_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2300_, v_msg_2301_, v_declHint_2302_, v___y_2303_, v___y_2304_);
    return v___x_2306_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11___boxed(
    mut v_00_u03b1_2307_: *mut leanh::LeanObject,
    mut v_ref_2308_: *mut leanh::LeanObject,
    mut v_msg_2309_: *mut leanh::LeanObject,
    mut v_declHint_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2314_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_2307_, v_ref_2308_, v_msg_2309_, v_declHint_2310_, v___y_2311_, v___y_2312_);
    leanh::lean_dec(v___y_2312_);
    leanh::lean_dec_ref(v___y_2311_);
    leanh::lean_dec(v_ref_2308_);
    return v_res_2314_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17(
    mut v_msg_2315_: *mut leanh::LeanObject,
    mut v_declHint_2316_: *mut leanh::LeanObject,
    mut v___y_2317_: *mut leanh::LeanObject,
    mut v___y_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2320_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___redArg(v_msg_2315_, v_declHint_2316_, v___y_2318_);
    return v___x_2320_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17___boxed(
    mut v_msg_2321_: *mut leanh::LeanObject,
    mut v_declHint_2322_: *mut leanh::LeanObject,
    mut v___y_2323_: *mut leanh::LeanObject,
    mut v___y_2324_: *mut leanh::LeanObject,
    mut v___y_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__15_spec__17(v_msg_2321_, v_declHint_2322_, v___y_2323_, v___y_2324_);
    leanh::lean_dec(v___y_2324_);
    leanh::lean_dec_ref(v___y_2323_);
    return v_res_2326_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16(
    mut v_00_u03b1_2327_: *mut leanh::LeanObject,
    mut v_ref_2328_: *mut leanh::LeanObject,
    mut v_msg_2329_: *mut leanh::LeanObject,
    mut v___y_2330_: *mut leanh::LeanObject,
    mut v___y_2331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___redArg(v_ref_2328_, v_msg_2329_, v___y_2330_, v___y_2331_);
    return v___x_2333_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16___boxed(
    mut v_00_u03b1_2334_: *mut leanh::LeanObject,
    mut v_ref_2335_: *mut leanh::LeanObject,
    mut v_msg_2336_: *mut leanh::LeanObject,
    mut v___y_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2340_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16(v_00_u03b1_2334_, v_ref_2335_, v_msg_2336_, v___y_2337_, v___y_2338_);
    leanh::lean_dec(v___y_2338_);
    leanh::lean_dec_ref(v___y_2337_);
    leanh::lean_dec(v_ref_2335_);
    return v_res_2340_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19(
    mut v_00_u03b1_2341_: *mut leanh::LeanObject,
    mut v_msg_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___redArg(v_msg_2342_, v___y_2343_, v___y_2344_);
    return v___x_2346_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19___boxed(
    mut v_00_u03b1_2347_: *mut leanh::LeanObject,
    mut v_msg_2348_: *mut leanh::LeanObject,
    mut v___y_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2352_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00getCasesInfo_x3f_spec__0_spec__0_spec__4_spec__11_spec__16_spec__19(v_00_u03b1_2347_, v_msg_2348_, v___y_2349_, v___y_2350_);
    leanh::lean_dec(v___y_2350_);
    leanh::lean_dec_ref(v___y_2349_);
    return v_res_2352_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CasesInfo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
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
pub unsafe fn meta_initialize_Lean_Meta_CasesInfo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CasesInfo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CasesInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CasesInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_CasesInfo(builtin);
}