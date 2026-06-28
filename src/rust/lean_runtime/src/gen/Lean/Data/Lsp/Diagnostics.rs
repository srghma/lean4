// Lean compiler output
// Module: Lean.Data.Lsp.Diagnostics
// Imports: Lean.Data.Lsp.Basic Lean.Data.Lsp.Utf16
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_instBEq___redArg___lam__0___boxed,
    l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_flatMapTR_go;
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_id___boxed,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqBool___boxed,
    l_instDecidableEqString___boxed,
};
use crate::r#gen::Lean::Data::Json::Basic::{
    l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27, l_Lean_Json_getBool_x3f,
    l_Lean_Json_getBool_x3f___boxed, l_Lean_Json_getInt_x3f, l_Lean_Json_getNat_x3f,
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_instBEq___private__1___boxed,
    l_Lean_Json_mkObj, l_Lean_JsonNumber_fromInt, l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Array_fromJson_x3f, l_Array_toJson, l_Lean_Json_getObjValAs_x3f___redArg,
    l_Lean_Json_opt___redArg, l_Lean_instFromJsonJson___lam__0,
    l_Lean_instToJsonBool___lam__0___boxed, l_Lean_instToJsonString___lam__0,
    l_Option_fromJson_x3f,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    initialize_Lean_Data_Lsp_Basic, l_Lean_Lsp_instBEqLocation_beq,
    l_Lean_Lsp_instFromJsonLocation_fromJson, l_Lean_Lsp_instInhabitedLocation_default,
    l_Lean_Lsp_instOrdLocation_ord, l_Lean_Lsp_instToJsonLocation_toJson,
    runtime_initialize_Lean_Data_Lsp_Basic,
};
use crate::r#gen::Lean::Data::Lsp::BasicAux::{
    l_Lean_Lsp_instBEqRange_beq, l_Lean_Lsp_instBEqRange_beq___boxed,
    l_Lean_Lsp_instFromJsonRange_fromJson, l_Lean_Lsp_instInhabitedRange_default,
    l_Lean_Lsp_instToJsonRange_toJson,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::{
    initialize_Lean_Data_Lsp_Utf16, runtime_initialize_Lean_Data_Lsp_Utf16,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Ord::String::lean_string_compare;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
    lean_string_dec_eq,
};
pub static mut l_Lean_Lsp_instInhabitedDiagnosticSeverity_default: u8 = 0;
pub static mut l_Lean_Lsp_instInhabitedDiagnosticSeverity: u8 = 0;
pub static l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqDiagnosticSeverity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdDiagnosticSeverity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 83,
        101, 118, 101, 114, 105, 116, 121, 32, 39, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDiagnosticSeverity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Lsp_instInhabitedDiagnosticCode: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instBEqDiagnosticCode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqDiagnosticCode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instOrdDiagnosticCode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdDiagnosticCode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0_value:
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 111, 114, 32,
        105, 110, 116, 101, 103, 101, 114, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32,
        99, 111, 100, 101, 44, 32, 103, 111, 116, 32, 39, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDiagnosticCode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instToJsonDiagnosticCode___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticCode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDiagnosticCode: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedDiagnosticTag_default: u8 = 0;
pub static mut l_Lean_Lsp_instInhabitedDiagnosticTag: u8 = 0;
pub static l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instBEqDiagnosticTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqDiagnosticTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instOrdDiagnosticTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdDiagnosticTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value:
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
        117, 110, 107, 110, 111, 119, 110, 32, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 84,
        97, 103, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDiagnosticTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDiagnosticTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default: u8 = 0;
pub static mut l_Lean_Lsp_instInhabitedLeanDiagnosticTag: u8 = 0;
pub static l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqLeanDiagnosticTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdLeanDiagnosticTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 76, 101, 97, 110, 68, 105, 97, 103, 110, 111, 115,
        116, 105, 99, 84, 97, 103, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_value:
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
static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_value:
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
static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanDiagnosticTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value:
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
static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value:
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
    m_fun: l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqDiagnosticRelatedInformation: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value:
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
    m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 101, 115, 115, 97, 103, 101, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_value:
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
static mut l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDiagnosticRelatedInformation: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value:
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
    m_data: [76, 115, 112, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 82, 101, 108, 97, 116, 101, 100, 73, 110,
        102, 111, 114, 109, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        3503059123801703312 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11490083008225922661 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 32, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        982637797389909653 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value:
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
    m_fun: l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdDiagnosticRelatedInformation: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value:
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
    m_fun: l_Lean_Lsp_instBEqRange_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_value:
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
    m_fun: l_Array_instBEq___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value:
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
    m_fun: l_Array_instBEq___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value:
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
    m_fun: l_Array_instBEq___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value:
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
    m_fun: l_Lean_Json_instBEq___private__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonRange_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value:
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
    m_fun: l_Lean_instToJsonBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value:
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
    m_fun: l_Lean_instToJsonString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_toJson as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_toJson as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_toJson as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6_value:
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
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value:
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
    m_data: [114, 97, 110, 103, 101, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8_value:
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
    m_data: [102, 117, 108, 108, 82, 97, 110, 103, 101, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9_value:
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
    m_data: [115, 101, 118, 101, 114, 105, 116, 121, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10_value:
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
    m_data: [105, 115, 83, 105, 108, 101, 110, 116, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11_value:
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
    m_data: [99, 111, 100, 101, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12_value:
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
    m_data: [115, 111, 117, 114, 99, 101, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13_value:
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
    m_data: [116, 97, 103, 115, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14_value:
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
    m_data: [108, 101, 97, 110, 84, 97, 103, 115, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
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
        114, 101, 108, 97, 116, 101, 100, 73, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16_value:
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
    m_data: [100, 97, 116, 97, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonRange_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 87, 105, 116, 104, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        2863902399367947479 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        12743603005877258865 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value:
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
    m_data: [102, 117, 108, 108, 82, 97, 110, 103, 101, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        18167956084314672844 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value:
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
    m_data: [115, 101, 118, 101, 114, 105, 116, 121, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value
        ) as *mut crate::leanh::LeanObject,
        2339750138993587592 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value:
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
    m_fun: l_Lean_Json_getBool_x3f___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value:
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
    m_data: [105, 115, 83, 105, 108, 101, 110, 116, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value
        ) as *mut crate::leanh::LeanObject,
        6916285088056307392 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value:
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
    m_data: [99, 111, 100, 101, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value
        ) as *mut crate::leanh::LeanObject,
        3386430046879539552 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value:
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
    m_fun: l_Lean_Json_getStr_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 111, 117, 114, 99, 101, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value
        ) as *mut crate::leanh::LeanObject,
        7764395542335372806 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value:
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
    m_data: [116, 97, 103, 115, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value
        ) as *mut crate::leanh::LeanObject,
        10757207218291958112 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value:
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
    m_data: [108, 101, 97, 110, 84, 97, 103, 115, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value
        ) as *mut crate::leanh::LeanObject,
        7655102125566572746 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        114, 101, 108, 97, 116, 101, 100, 73, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 63,
        0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value
        ) as *mut crate::leanh::LeanObject,
        15798532268063128341 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value:
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
    m_fun: l_Lean_instFromJsonJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value:
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
    m_data: [100, 97, 116, 97, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value
        ) as *mut crate::leanh::LeanObject,
        14378392202104151310 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value:
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
static mut l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedPublishDiagnosticsParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqPublishDiagnosticsParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value:
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
    m_data: [117, 114, 105, 0],
};
static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [118, 101, 114, 115, 105, 111, 110, 0],
};
static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value:
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
        105, 115, 73, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value:
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
    m_data: [100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 0],
};
static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value:
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
        80, 117, 98, 108, 105, 115, 104, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 80,
        97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        18094239079051600156 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6053811214292724070 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value:
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
    m_data: [118, 101, 114, 115, 105, 111, 110, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        5707914067652744443 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        105, 115, 73, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_value:
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        2214070583702819421 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value)
            as *mut crate::leanh::LeanObject,
        16258271359659748332 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorIdx(
    mut v_x_2822_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2822_ {
        0 => {
            let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2823_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2823_;
        }
        1 => {
            let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2824_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2824_;
        }
        2 => {
            let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2825_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2825_;
        }
        _ => {
            let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2826_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2826_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorIdx___boxed(
    mut v_x_2827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2828_: u8 = 0;
    let mut v_res_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2828_ = (crate::leanh::lean_unbox(v_x_2827_) as u8);
    v_res_2829_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_boxed_2828_);
    return v_res_2829_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(
    mut v_x_2830_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_2830_);
    return v___x_2831_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_toCtorIdx___boxed(
    mut v_x_2832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_2833_: u8 = 0;
    let mut v_res_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2833_ = (crate::leanh::lean_unbox(v_x_2832_) as u8);
    v_res_2834_ = l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(v_x_4__boxed_2833_);
    return v_res_2834_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(
    mut v_k_2835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2835_);
    return v_k_2835_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg___boxed(
    mut v_k_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2837_ = l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(v_k_2836_);
    crate::leanh::lean_dec(v_k_2836_);
    return v_res_2837_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorElim(
    mut v_motive_2838_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2839_: *mut crate::leanh::LeanObject,
    mut v_t_2840_: u8,
    mut v_h_2841_: *mut crate::leanh::LeanObject,
    mut v_k_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2842_);
    return v_k_2842_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorElim___boxed(
    mut v_motive_2843_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2844_: *mut crate::leanh::LeanObject,
    mut v_t_2845_: *mut crate::leanh::LeanObject,
    mut v_h_2846_: *mut crate::leanh::LeanObject,
    mut v_k_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2848_: u8 = 0;
    let mut v_res_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2848_ = (crate::leanh::lean_unbox(v_t_2845_) as u8);
    v_res_2849_ = l_Lean_Lsp_DiagnosticSeverity_ctorElim(
        v_motive_2843_,
        v_ctorIdx_2844_,
        v_t_boxed_2848_,
        v_h_2846_,
        v_k_2847_,
    );
    crate::leanh::lean_dec(v_k_2847_);
    crate::leanh::lean_dec(v_ctorIdx_2844_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(
    mut v_error_2850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_error_2850_);
    return v_error_2850_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg___boxed(
    mut v_error_2851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(v_error_2851_);
    crate::leanh::lean_dec(v_error_2851_);
    return v_res_2852_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_error_elim(
    mut v_motive_2853_: *mut crate::leanh::LeanObject,
    mut v_t_2854_: u8,
    mut v_h_2855_: *mut crate::leanh::LeanObject,
    mut v_error_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_error_2856_);
    return v_error_2856_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_error_elim___boxed(
    mut v_motive_2857_: *mut crate::leanh::LeanObject,
    mut v_t_2858_: *mut crate::leanh::LeanObject,
    mut v_h_2859_: *mut crate::leanh::LeanObject,
    mut v_error_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2861_: u8 = 0;
    let mut v_res_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2861_ = (crate::leanh::lean_unbox(v_t_2858_) as u8);
    v_res_2862_ = l_Lean_Lsp_DiagnosticSeverity_error_elim(
        v_motive_2857_,
        v_t_boxed_2861_,
        v_h_2859_,
        v_error_2860_,
    );
    crate::leanh::lean_dec(v_error_2860_);
    return v_res_2862_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(
    mut v_warning_2863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_warning_2863_);
    return v_warning_2863_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg___boxed(
    mut v_warning_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(v_warning_2864_);
    crate::leanh::lean_dec(v_warning_2864_);
    return v_res_2865_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_warning_elim(
    mut v_motive_2866_: *mut crate::leanh::LeanObject,
    mut v_t_2867_: u8,
    mut v_h_2868_: *mut crate::leanh::LeanObject,
    mut v_warning_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_warning_2869_);
    return v_warning_2869_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_warning_elim___boxed(
    mut v_motive_2870_: *mut crate::leanh::LeanObject,
    mut v_t_2871_: *mut crate::leanh::LeanObject,
    mut v_h_2872_: *mut crate::leanh::LeanObject,
    mut v_warning_2873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2874_: u8 = 0;
    let mut v_res_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2874_ = (crate::leanh::lean_unbox(v_t_2871_) as u8);
    v_res_2875_ = l_Lean_Lsp_DiagnosticSeverity_warning_elim(
        v_motive_2870_,
        v_t_boxed_2874_,
        v_h_2872_,
        v_warning_2873_,
    );
    crate::leanh::lean_dec(v_warning_2873_);
    return v_res_2875_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(
    mut v_information_2876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_information_2876_);
    return v_information_2876_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg___boxed(
    mut v_information_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2878_ = l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(v_information_2877_);
    crate::leanh::lean_dec(v_information_2877_);
    return v_res_2878_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_information_elim(
    mut v_motive_2879_: *mut crate::leanh::LeanObject,
    mut v_t_2880_: u8,
    mut v_h_2881_: *mut crate::leanh::LeanObject,
    mut v_information_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_information_2882_);
    return v_information_2882_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_information_elim___boxed(
    mut v_motive_2883_: *mut crate::leanh::LeanObject,
    mut v_t_2884_: *mut crate::leanh::LeanObject,
    mut v_h_2885_: *mut crate::leanh::LeanObject,
    mut v_information_2886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2887_: u8 = 0;
    let mut v_res_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2887_ = (crate::leanh::lean_unbox(v_t_2884_) as u8);
    v_res_2888_ = l_Lean_Lsp_DiagnosticSeverity_information_elim(
        v_motive_2883_,
        v_t_boxed_2887_,
        v_h_2885_,
        v_information_2886_,
    );
    crate::leanh::lean_dec(v_information_2886_);
    return v_res_2888_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(
    mut v_hint_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_hint_2889_);
    return v_hint_2889_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg___boxed(
    mut v_hint_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2891_ = l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(v_hint_2890_);
    crate::leanh::lean_dec(v_hint_2890_);
    return v_res_2891_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_hint_elim(
    mut v_motive_2892_: *mut crate::leanh::LeanObject,
    mut v_t_2893_: u8,
    mut v_h_2894_: *mut crate::leanh::LeanObject,
    mut v_hint_2895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_hint_2895_);
    return v_hint_2895_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_hint_elim___boxed(
    mut v_motive_2896_: *mut crate::leanh::LeanObject,
    mut v_t_2897_: *mut crate::leanh::LeanObject,
    mut v_h_2898_: *mut crate::leanh::LeanObject,
    mut v_hint_2899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2900_: u8 = 0;
    let mut v_res_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2900_ = (crate::leanh::lean_unbox(v_t_2897_) as u8);
    v_res_2901_ = l_Lean_Lsp_DiagnosticSeverity_hint_elim(
        v_motive_2896_,
        v_t_boxed_2900_,
        v_h_2898_,
        v_hint_2899_,
    );
    crate::leanh::lean_dec(v_hint_2899_);
    return v_res_2901_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity_default() -> u8 {
    let mut v___x_2902_: u8 = 0;
    v___x_2902_ = 0;
    return v___x_2902_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity() -> u8 {
    let mut v___x_2903_: u8 = 0;
    v___x_2903_ = 0;
    return v___x_2903_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticSeverity_beq(mut v_x_2904_: u8, mut v_y_2905_: u8) -> u8 {
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: u8 = 0;
    v___x_2906_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_2904_);
    v___x_2907_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_y_2905_);
    v___x_2908_ = lean_nat_dec_eq(v___x_2906_, v___x_2907_);
    crate::leanh::lean_dec(v___x_2907_);
    crate::leanh::lean_dec(v___x_2906_);
    return v___x_2908_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed(
    mut v_x_2909_: *mut crate::leanh::LeanObject,
    mut v_y_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_2911_: u8 = 0;
    let mut v_y_18__boxed_2912_: u8 = 0;
    let mut v_res_2913_: u8 = 0;
    let mut v_r_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2911_ = (crate::leanh::lean_unbox(v_x_2909_) as u8);
    v_y_18__boxed_2912_ = (crate::leanh::lean_unbox(v_y_2910_) as u8);
    v_res_2913_ =
        l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v_x_17__boxed_2911_, v_y_18__boxed_2912_);
    v_r_2914_ = crate::leanh::lean_box((v_res_2913_) as usize);
    return v_r_2914_;
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticSeverity_ord(mut v_x_2917_: u8, mut v_y_2918_: u8) -> u8 {
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    v___x_2919_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_2917_);
    v___x_2920_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_y_2918_);
    v___x_2921_ = lean_nat_dec_lt(v___x_2919_, v___x_2920_);
    if v___x_2921_ == 0 {
        let mut v___x_2922_: u8 = 0;
        v___x_2922_ = lean_nat_dec_eq(v___x_2919_, v___x_2920_);
        crate::leanh::lean_dec(v___x_2920_);
        crate::leanh::lean_dec(v___x_2919_);
        if v___x_2922_ == 0 {
            let mut v___x_2923_: u8 = 0;
            v___x_2923_ = 2;
            return v___x_2923_;
        } else {
            let mut v___x_2924_: u8 = 0;
            v___x_2924_ = 1;
            return v___x_2924_;
        }
    } else {
        let mut v___x_2925_: u8 = 0;
        crate::leanh::lean_dec(v___x_2920_);
        crate::leanh::lean_dec(v___x_2919_);
        v___x_2925_ = 0;
        return v___x_2925_;
    }
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed(
    mut v_x_2926_: *mut crate::leanh::LeanObject,
    mut v_y_2927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_2928_: u8 = 0;
    let mut v_y_31__boxed_2929_: u8 = 0;
    let mut v_res_2930_: u8 = 0;
    let mut v_r_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_2928_ = (crate::leanh::lean_unbox(v_x_2926_) as u8);
    v_y_31__boxed_2929_ = (crate::leanh::lean_unbox(v_y_2927_) as u8);
    v_res_2930_ =
        l_Lean_Lsp_instOrdDiagnosticSeverity_ord(v_x_30__boxed_2928_, v_y_31__boxed_2929_);
    v_r_2931_ = crate::leanh::lean_box((v_res_2930_) as usize);
    return v_r_2931_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0(
    mut v_j_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: u8 = 0;
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_j_2948_);
                v___x_2957_ = l_Lean_Json_getNat_x3f(v_j_2948_);
                if crate::leanh::lean_obj_tag(v___x_2957_) == 1 {
                    v_a_2958_ = crate::leanh::lean_ctor_get(v___x_2957_, 0);
                    crate::leanh::lean_inc(v_a_2958_);
                    crate::leanh::lean_dec_ref_known(v___x_2957_, 1);
                    v___x_2959_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2960_ = lean_nat_dec_eq(v_a_2958_, v___x_2959_);
                    if v___x_2960_ == 0 {
                        v___x_2961_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2962_ = lean_nat_dec_eq(v_a_2958_, v___x_2961_);
                        if v___x_2962_ == 0 {
                            v___x_2963_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2964_ = lean_nat_dec_eq(v_a_2958_, v___x_2963_);
                            if v___x_2964_ == 0 {
                                v___x_2965_ = crate::leanh::lean_unsigned_to_nat(4);
                                v___x_2966_ = lean_nat_dec_eq(v_a_2958_, v___x_2965_);
                                crate::leanh::lean_dec(v_a_2958_);
                                if v___x_2966_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_j_2948_);
                                    v___x_2967_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2;
                                    return v___x_2967_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2958_);
                                crate::leanh::lean_dec(v_j_2948_);
                                v___x_2968_ =
                                    l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3;
                                return v___x_2968_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2958_);
                            crate::leanh::lean_dec(v_j_2948_);
                            v___x_2969_ =
                                l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4;
                            return v___x_2969_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2958_);
                        crate::leanh::lean_dec(v_j_2948_);
                        v___x_2970_ =
                            l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5;
                        return v___x_2970_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2957_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2950_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0;
                v___x_2951_ = crate::leanh::lean_unsigned_to_nat(80);
                v___x_2952_ = l_Lean_Json_pretty(v_j_2948_, v___x_2951_);
                v___x_2953_ = lean_string_append(v___x_2950_, v___x_2952_);
                crate::leanh::lean_dec_ref(v___x_2952_);
                v___x_2954_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
                v___x_2955_ = lean_string_append(v___x_2953_, v___x_2954_);
                v___x_2956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2956_, 0, v___x_2955_);
                return v___x_2956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2973_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2974_ = l_Lean_JsonNumber_fromNat(v___x_2973_);
    return v___x_2974_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2975_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0_once),
        _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0,
    );
    v___x_2976_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2976_, 0, v___x_2975_);
    return v___x_2976_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2977_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2978_ = l_Lean_JsonNumber_fromNat(v___x_2977_);
    return v___x_2978_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2979_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2_once),
        _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2,
    );
    v___x_2980_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2980_, 0, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2981_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2982_ = l_Lean_JsonNumber_fromNat(v___x_2981_);
    return v___x_2982_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4_once),
        _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4,
    );
    v___x_2984_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2984_, 0, v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2985_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2986_ = l_Lean_JsonNumber_fromNat(v___x_2985_);
    return v___x_2986_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2987_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6_once),
        _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6,
    );
    v___x_2988_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2988_, 0, v___x_2987_);
    return v___x_2988_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(
    mut v_x_2989_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2989_ {
        0 => {
            let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2990_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once
                ),
                _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1,
            );
            return v___x_2990_;
        }
        1 => {
            let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2991_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once
                ),
                _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3,
            );
            return v___x_2991_;
        }
        2 => {
            let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2992_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once
                ),
                _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5,
            );
            return v___x_2992_;
        }
        _ => {
            let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2993_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once
                ),
                _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7,
            );
            return v___x_2993_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed(
    mut v_x_2994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_106__boxed_2995_: u8 = 0;
    let mut v_res_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_106__boxed_2995_ = (crate::leanh::lean_unbox(v_x_2994_) as u8);
    v_res_2996_ = l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(v_x_106__boxed_2995_);
    return v_res_2996_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorIdx(
    mut v_x_2999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2999_) == 0 {
        let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3000_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3000_;
    } else {
        let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3001_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3001_;
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorIdx___boxed(
    mut v_x_3002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3003_ = l_Lean_Lsp_DiagnosticCode_ctorIdx(v_x_3002_);
    crate::leanh::lean_dec_ref(v_x_3002_);
    return v_res_3003_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(
    mut v_t_3004_: *mut crate::leanh::LeanObject,
    mut v_k_3005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3004_) == 0 {
        let mut v_i_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_i_3006_ = crate::leanh::lean_ctor_get(v_t_3004_, 0);
        crate::leanh::lean_inc(v_i_3006_);
        crate::leanh::lean_dec_ref_known(v_t_3004_, 1);
        v___x_3007_ = crate::leanh::lean_apply_1(v_k_3005_, v_i_3006_);
        return v___x_3007_;
    } else {
        let mut v_s_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_s_3008_ = crate::leanh::lean_ctor_get(v_t_3004_, 0);
        crate::leanh::lean_inc_ref(v_s_3008_);
        crate::leanh::lean_dec_ref_known(v_t_3004_, 1);
        v___x_3009_ = crate::leanh::lean_apply_1(v_k_3005_, v_s_3008_);
        return v___x_3009_;
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorElim(
    mut v_motive_3010_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3011_: *mut crate::leanh::LeanObject,
    mut v_t_3012_: *mut crate::leanh::LeanObject,
    mut v_h_3013_: *mut crate::leanh::LeanObject,
    mut v_k_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3015_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3012_, v_k_3014_);
    return v___x_3015_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorElim___boxed(
    mut v_motive_3016_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3017_: *mut crate::leanh::LeanObject,
    mut v_t_3018_: *mut crate::leanh::LeanObject,
    mut v_h_3019_: *mut crate::leanh::LeanObject,
    mut v_k_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Lean_Lsp_DiagnosticCode_ctorElim(
        v_motive_3016_,
        v_ctorIdx_3017_,
        v_t_3018_,
        v_h_3019_,
        v_k_3020_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3017_);
    return v_res_3021_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_int_elim___redArg(
    mut v_t_3022_: *mut crate::leanh::LeanObject,
    mut v_int_3023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3024_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3022_, v_int_3023_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_int_elim(
    mut v_motive_3025_: *mut crate::leanh::LeanObject,
    mut v_t_3026_: *mut crate::leanh::LeanObject,
    mut v_h_3027_: *mut crate::leanh::LeanObject,
    mut v_int_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3029_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3026_, v_int_3028_);
    return v___x_3029_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_string_elim___redArg(
    mut v_t_3030_: *mut crate::leanh::LeanObject,
    mut v_string_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3030_, v_string_3031_);
    return v___x_3032_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_string_elim(
    mut v_motive_3033_: *mut crate::leanh::LeanObject,
    mut v_t_3034_: *mut crate::leanh::LeanObject,
    mut v_h_3035_: *mut crate::leanh::LeanObject,
    mut v_string_3036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3037_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3034_, v_string_3036_);
    return v___x_3037_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3038_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3039_ = lean_nat_to_int(v___x_3038_);
    return v___x_3039_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3040_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once),
        _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0,
    );
    v___x_3041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3041_, 0, v___x_3040_);
    return v___x_3041_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3042_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once),
        _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1,
    );
    return v___x_3042_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticCode() -> *mut crate::leanh::LeanObject {
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = l_Lean_Lsp_instInhabitedDiagnosticCode_default;
    return v___x_3043_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticCode_beq(
    mut v_x_3044_: *mut crate::leanh::LeanObject,
    mut v_x_3045_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3044_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_3045_) == 0 {
            let mut v_i_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3048_: u8 = 0;
            v_i_3046_ = crate::leanh::lean_ctor_get(v_x_3044_, 0);
            v_i_3047_ = crate::leanh::lean_ctor_get(v_x_3045_, 0);
            v___x_3048_ = lean_int_dec_eq(v_i_3046_, v_i_3047_);
            return v___x_3048_;
        } else {
            let mut v___x_3049_: u8 = 0;
            v___x_3049_ = 0;
            return v___x_3049_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_3045_) == 1 {
            let mut v_s_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3052_: u8 = 0;
            v_s_3050_ = crate::leanh::lean_ctor_get(v_x_3044_, 0);
            v_s_3051_ = crate::leanh::lean_ctor_get(v_x_3045_, 0);
            v___x_3052_ = lean_string_dec_eq(v_s_3050_, v_s_3051_);
            return v___x_3052_;
        } else {
            let mut v___x_3053_: u8 = 0;
            v___x_3053_ = 0;
            return v___x_3053_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed(
    mut v_x_3054_: *mut crate::leanh::LeanObject,
    mut v_x_3055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3056_: u8 = 0;
    let mut v_r_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_x_3054_, v_x_3055_);
    crate::leanh::lean_dec_ref(v_x_3055_);
    crate::leanh::lean_dec_ref(v_x_3054_);
    v_r_3057_ = crate::leanh::lean_box((v_res_3056_) as usize);
    return v_r_3057_;
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticCode_ord(
    mut v_x_3060_: *mut crate::leanh::LeanObject,
    mut v_x_3061_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3060_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_3061_) == 0 {
            let mut v_i_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3064_: u8 = 0;
            v_i_3062_ = crate::leanh::lean_ctor_get(v_x_3060_, 0);
            v_i_3063_ = crate::leanh::lean_ctor_get(v_x_3061_, 0);
            v___x_3064_ = lean_int_dec_lt(v_i_3062_, v_i_3063_);
            if v___x_3064_ == 0 {
                let mut v___x_3065_: u8 = 0;
                v___x_3065_ = lean_int_dec_eq(v_i_3062_, v_i_3063_);
                if v___x_3065_ == 0 {
                    let mut v___x_3066_: u8 = 0;
                    v___x_3066_ = 2;
                    return v___x_3066_;
                } else {
                    let mut v___x_3067_: u8 = 0;
                    v___x_3067_ = 1;
                    return v___x_3067_;
                }
            } else {
                let mut v___x_3068_: u8 = 0;
                v___x_3068_ = 0;
                return v___x_3068_;
            }
        } else {
            let mut v___x_3069_: u8 = 0;
            v___x_3069_ = 0;
            return v___x_3069_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_3061_) == 0 {
            let mut v___x_3070_: u8 = 0;
            v___x_3070_ = 2;
            return v___x_3070_;
        } else {
            let mut v_s_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3073_: u8 = 0;
            v_s_3071_ = crate::leanh::lean_ctor_get(v_x_3060_, 0);
            v_s_3072_ = crate::leanh::lean_ctor_get(v_x_3061_, 0);
            v___x_3073_ = lean_string_compare(v_s_3071_, v_s_3072_);
            if v___x_3073_ == 1 {
                return v___x_3073_;
            } else {
                return v___x_3073_;
            }
        }
    }
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed(
    mut v_x_3074_: *mut crate::leanh::LeanObject,
    mut v_x_3075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3076_: u8 = 0;
    let mut v_r_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3076_ = l_Lean_Lsp_instOrdDiagnosticCode_ord(v_x_3074_, v_x_3075_);
    crate::leanh::lean_dec_ref(v_x_3075_);
    crate::leanh::lean_dec_ref(v_x_3074_);
    v_r_3077_ = crate::leanh::lean_box((v_res_3076_) as usize);
    return v_r_3077_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0(
    mut v_x_3081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut v_unused_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3081_) {
                2 => {
                    v_n_3090_ = crate::leanh::lean_ctor_get(v_x_3081_, 0);
                    v_mantissa_3091_ = crate::leanh::lean_ctor_get(v_n_3090_, 0);
                    v_exponent_3092_ = crate::leanh::lean_ctor_get(v_n_3090_, 1);
                    v___x_3093_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3094_ = lean_nat_dec_eq(v_exponent_3092_, v___x_3093_);
                    if v___x_3094_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mantissa_3091_);
                        v_isSharedCheck_3102_ = (!crate::leanh::lean_is_exclusive(v_x_3081_)) as u8;
                        if v_isSharedCheck_3102_ == 0 {
                            v_unused_3103_ = crate::leanh::lean_ctor_get(v_x_3081_, 0);
                            crate::leanh::lean_dec(v_unused_3103_);
                            v___x_3096_ = v_x_3081_;
                            v_isShared_3097_ = v_isSharedCheck_3102_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3081_);
                            v___x_3096_ = crate::leanh::lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3102_;
                            state = 2;
                            continue;
                        }
                    }
                }
                3 => {
                    v_s_3104_ = crate::leanh::lean_ctor_get(v_x_3081_, 0);
                    v_isSharedCheck_3112_ = (!crate::leanh::lean_is_exclusive(v_x_3081_)) as u8;
                    if v_isSharedCheck_3112_ == 0 {
                        v___x_3106_ = v_x_3081_;
                        v_isShared_3107_ = v_isSharedCheck_3112_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_3104_);
                        crate::leanh::lean_dec(v_x_3081_);
                        v___x_3106_ = crate::leanh::lean_box(0);
                        v_isShared_3107_ = v_isSharedCheck_3112_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_3083_ = l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0;
                v___x_3084_ = crate::leanh::lean_unsigned_to_nat(80);
                v___x_3085_ = l_Lean_Json_pretty(v_x_3081_, v___x_3084_);
                v___x_3086_ = lean_string_append(v___x_3083_, v___x_3085_);
                crate::leanh::lean_dec_ref(v___x_3085_);
                v___x_3087_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
                v___x_3088_ = lean_string_append(v___x_3086_, v___x_3087_);
                v___x_3089_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3089_, 0, v___x_3088_);
                return v___x_3089_;
            }
            2 => {
                if v_isShared_3097_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3096_, 0);
                    crate::leanh::lean_ctor_set(v___x_3096_, 0, v_mantissa_3091_);
                    v___x_3099_ = v___x_3096_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3101_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_mantissa_3091_);
                    v___x_3099_ = v_reuseFailAlloc_3101_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3100_, 0, v___x_3099_);
                return v___x_3100_;
            }
            4 => {
                if v_isShared_3107_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3106_, 1);
                    v___x_3109_ = v___x_3106_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_s_3104_);
                    v___x_3109_ = v_reuseFailAlloc_3111_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3110_, 0, v___x_3109_);
                return v___x_3110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticCode___lam__0(
    mut v_x_3115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_s_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3115_) == 0 {
                    v_i_3116_ = crate::leanh::lean_ctor_get(v_x_3115_, 0);
                    v_isSharedCheck_3124_ = (!crate::leanh::lean_is_exclusive(v_x_3115_)) as u8;
                    if v_isSharedCheck_3124_ == 0 {
                        v___x_3118_ = v_x_3115_;
                        v_isShared_3119_ = v_isSharedCheck_3124_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_i_3116_);
                        crate::leanh::lean_dec(v_x_3115_);
                        v___x_3118_ = crate::leanh::lean_box(0);
                        v_isShared_3119_ = v_isSharedCheck_3124_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_s_3125_ = crate::leanh::lean_ctor_get(v_x_3115_, 0);
                    v_isSharedCheck_3132_ = (!crate::leanh::lean_is_exclusive(v_x_3115_)) as u8;
                    if v_isSharedCheck_3132_ == 0 {
                        v___x_3127_ = v_x_3115_;
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_3125_);
                        crate::leanh::lean_dec(v_x_3115_);
                        v___x_3127_ = crate::leanh::lean_box(0);
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3120_ = l_Lean_JsonNumber_fromInt(v_i_3116_);
                if v_isShared_3119_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3118_, 2);
                    crate::leanh::lean_ctor_set(v___x_3118_, 0, v___x_3120_);
                    v___x_3122_ = v___x_3118_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3122_;
            }
            3 => {
                if v_isShared_3128_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3127_, 3);
                    v___x_3130_ = v___x_3127_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_s_3125_);
                    v___x_3130_ = v_reuseFailAlloc_3131_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorIdx(mut v_x_3135_: u8) -> *mut crate::leanh::LeanObject {
    if v_x_3135_ == 0 {
        let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3136_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3136_;
    } else {
        let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3137_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3137_;
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorIdx___boxed(
    mut v_x_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3139_: u8 = 0;
    let mut v_res_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3139_ = (crate::leanh::lean_unbox(v_x_3138_) as u8);
    v_res_3140_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_boxed_3139_);
    return v_res_3140_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_toCtorIdx(
    mut v_x_3141_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3142_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_3141_);
    return v___x_3142_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_toCtorIdx___boxed(
    mut v_x_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_3144_: u8 = 0;
    let mut v_res_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3144_ = (crate::leanh::lean_unbox(v_x_3143_) as u8);
    v_res_3145_ = l_Lean_Lsp_DiagnosticTag_toCtorIdx(v_x_4__boxed_3144_);
    return v_res_3145_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(
    mut v_k_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3146_);
    return v_k_3146_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorElim___redArg___boxed(
    mut v_k_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(v_k_3147_);
    crate::leanh::lean_dec(v_k_3147_);
    return v_res_3148_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorElim(
    mut v_motive_3149_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3150_: *mut crate::leanh::LeanObject,
    mut v_t_3151_: u8,
    mut v_h_3152_: *mut crate::leanh::LeanObject,
    mut v_k_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3153_);
    return v_k_3153_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorElim___boxed(
    mut v_motive_3154_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3155_: *mut crate::leanh::LeanObject,
    mut v_t_3156_: *mut crate::leanh::LeanObject,
    mut v_h_3157_: *mut crate::leanh::LeanObject,
    mut v_k_3158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3159_: u8 = 0;
    let mut v_res_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3159_ = (crate::leanh::lean_unbox(v_t_3156_) as u8);
    v_res_3160_ = l_Lean_Lsp_DiagnosticTag_ctorElim(
        v_motive_3154_,
        v_ctorIdx_3155_,
        v_t_boxed_3159_,
        v_h_3157_,
        v_k_3158_,
    );
    crate::leanh::lean_dec(v_k_3158_);
    crate::leanh::lean_dec(v_ctorIdx_3155_);
    return v_res_3160_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(
    mut v_unnecessary_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unnecessary_3161_);
    return v_unnecessary_3161_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg___boxed(
    mut v_unnecessary_3162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3163_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(v_unnecessary_3162_);
    crate::leanh::lean_dec(v_unnecessary_3162_);
    return v_res_3163_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_unnecessary_elim(
    mut v_motive_3164_: *mut crate::leanh::LeanObject,
    mut v_t_3165_: u8,
    mut v_h_3166_: *mut crate::leanh::LeanObject,
    mut v_unnecessary_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unnecessary_3167_);
    return v_unnecessary_3167_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_unnecessary_elim___boxed(
    mut v_motive_3168_: *mut crate::leanh::LeanObject,
    mut v_t_3169_: *mut crate::leanh::LeanObject,
    mut v_h_3170_: *mut crate::leanh::LeanObject,
    mut v_unnecessary_3171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3172_: u8 = 0;
    let mut v_res_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3172_ = (crate::leanh::lean_unbox(v_t_3169_) as u8);
    v_res_3173_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim(
        v_motive_3168_,
        v_t_boxed_3172_,
        v_h_3170_,
        v_unnecessary_3171_,
    );
    crate::leanh::lean_dec(v_unnecessary_3171_);
    return v_res_3173_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(
    mut v_deprecated_3174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_deprecated_3174_);
    return v_deprecated_3174_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg___boxed(
    mut v_deprecated_3175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(v_deprecated_3175_);
    crate::leanh::lean_dec(v_deprecated_3175_);
    return v_res_3176_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_deprecated_elim(
    mut v_motive_3177_: *mut crate::leanh::LeanObject,
    mut v_t_3178_: u8,
    mut v_h_3179_: *mut crate::leanh::LeanObject,
    mut v_deprecated_3180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_deprecated_3180_);
    return v_deprecated_3180_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_deprecated_elim___boxed(
    mut v_motive_3181_: *mut crate::leanh::LeanObject,
    mut v_t_3182_: *mut crate::leanh::LeanObject,
    mut v_h_3183_: *mut crate::leanh::LeanObject,
    mut v_deprecated_3184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3185_: u8 = 0;
    let mut v_res_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3185_ = (crate::leanh::lean_unbox(v_t_3182_) as u8);
    v_res_3186_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim(
        v_motive_3181_,
        v_t_boxed_3185_,
        v_h_3183_,
        v_deprecated_3184_,
    );
    crate::leanh::lean_dec(v_deprecated_3184_);
    return v_res_3186_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticTag_default() -> u8 {
    let mut v___x_3187_: u8 = 0;
    v___x_3187_ = 0;
    return v___x_3187_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticTag() -> u8 {
    let mut v___x_3188_: u8 = 0;
    v___x_3188_ = 0;
    return v___x_3188_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticTag_beq(mut v_x_3189_: u8, mut v_y_3190_: u8) -> u8 {
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: u8 = 0;
    v___x_3191_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_3189_);
    v___x_3192_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_y_3190_);
    v___x_3193_ = lean_nat_dec_eq(v___x_3191_, v___x_3192_);
    crate::leanh::lean_dec(v___x_3192_);
    crate::leanh::lean_dec(v___x_3191_);
    return v___x_3193_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed(
    mut v_x_3194_: *mut crate::leanh::LeanObject,
    mut v_y_3195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_3196_: u8 = 0;
    let mut v_y_18__boxed_3197_: u8 = 0;
    let mut v_res_3198_: u8 = 0;
    let mut v_r_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_3196_ = (crate::leanh::lean_unbox(v_x_3194_) as u8);
    v_y_18__boxed_3197_ = (crate::leanh::lean_unbox(v_y_3195_) as u8);
    v_res_3198_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v_x_17__boxed_3196_, v_y_18__boxed_3197_);
    v_r_3199_ = crate::leanh::lean_box((v_res_3198_) as usize);
    return v_r_3199_;
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticTag_ord(mut v_x_3202_: u8, mut v_y_3203_: u8) -> u8 {
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    v___x_3204_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_3202_);
    v___x_3205_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_y_3203_);
    v___x_3206_ = lean_nat_dec_lt(v___x_3204_, v___x_3205_);
    if v___x_3206_ == 0 {
        let mut v___x_3207_: u8 = 0;
        v___x_3207_ = lean_nat_dec_eq(v___x_3204_, v___x_3205_);
        crate::leanh::lean_dec(v___x_3205_);
        crate::leanh::lean_dec(v___x_3204_);
        if v___x_3207_ == 0 {
            let mut v___x_3208_: u8 = 0;
            v___x_3208_ = 2;
            return v___x_3208_;
        } else {
            let mut v___x_3209_: u8 = 0;
            v___x_3209_ = 1;
            return v___x_3209_;
        }
    } else {
        let mut v___x_3210_: u8 = 0;
        crate::leanh::lean_dec(v___x_3205_);
        crate::leanh::lean_dec(v___x_3204_);
        v___x_3210_ = 0;
        return v___x_3210_;
    }
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed(
    mut v_x_3211_: *mut crate::leanh::LeanObject,
    mut v_y_3212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_3213_: u8 = 0;
    let mut v_y_31__boxed_3214_: u8 = 0;
    let mut v_res_3215_: u8 = 0;
    let mut v_r_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_3213_ = (crate::leanh::lean_unbox(v_x_3211_) as u8);
    v_y_31__boxed_3214_ = (crate::leanh::lean_unbox(v_y_3212_) as u8);
    v_res_3215_ = l_Lean_Lsp_instOrdDiagnosticTag_ord(v_x_30__boxed_3213_, v_y_31__boxed_3214_);
    v_r_3216_ = crate::leanh::lean_box((v_res_3215_) as usize);
    return v_r_3216_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0(
    mut v_j_3228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u8 = 0;
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3231_ = l_Lean_Json_getNat_x3f(v_j_3228_);
                if crate::leanh::lean_obj_tag(v___x_3231_) == 1 {
                    v_a_3232_ = crate::leanh::lean_ctor_get(v___x_3231_, 0);
                    crate::leanh::lean_inc(v_a_3232_);
                    crate::leanh::lean_dec_ref_known(v___x_3231_, 1);
                    v___x_3233_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3234_ = lean_nat_dec_eq(v_a_3232_, v___x_3233_);
                    if v___x_3234_ == 0 {
                        v___x_3235_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_3236_ = lean_nat_dec_eq(v_a_3232_, v___x_3235_);
                        crate::leanh::lean_dec(v_a_3232_);
                        if v___x_3236_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_3237_ = l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2;
                            return v___x_3237_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3232_);
                        v___x_3238_ = l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3;
                        return v___x_3238_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3231_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3230_ = l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1;
                return v___x_3230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(
    mut v_x_3241_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_3241_ == 0 {
        let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3242_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once
            ),
            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1,
        );
        return v___x_3242_;
    } else {
        let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3243_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once
            ),
            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3,
        );
        return v___x_3243_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed(
    mut v_x_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_48__boxed_3245_: u8 = 0;
    let mut v_res_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_48__boxed_3245_ = (crate::leanh::lean_unbox(v_x_3244_) as u8);
    v_res_3246_ = l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(v_x_48__boxed_3245_);
    return v_res_3246_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(
    mut v_x_3249_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_3249_ == 0 {
        let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3250_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3250_;
    } else {
        let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3251_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3251_;
    }
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___boxed(
    mut v_x_3252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3253_: u8 = 0;
    let mut v_res_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3253_ = (crate::leanh::lean_unbox(v_x_3252_) as u8);
    v_res_3254_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_boxed_3253_);
    return v_res_3254_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(
    mut v_x_3255_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx___boxed(
    mut v_x_3257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_3258_: u8 = 0;
    let mut v_res_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3258_ = (crate::leanh::lean_unbox(v_x_3257_) as u8);
    v_res_3259_ = l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(v_x_4__boxed_3258_);
    return v_res_3259_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(
    mut v_k_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3260_);
    return v_k_3260_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg___boxed(
    mut v_k_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3262_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(v_k_3261_);
    crate::leanh::lean_dec(v_k_3261_);
    return v_res_3262_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorElim(
    mut v_motive_3263_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3264_: *mut crate::leanh::LeanObject,
    mut v_t_3265_: u8,
    mut v_h_3266_: *mut crate::leanh::LeanObject,
    mut v_k_3267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3267_);
    return v_k_3267_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorElim___boxed(
    mut v_motive_3268_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3269_: *mut crate::leanh::LeanObject,
    mut v_t_3270_: *mut crate::leanh::LeanObject,
    mut v_h_3271_: *mut crate::leanh::LeanObject,
    mut v_k_3272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3273_: u8 = 0;
    let mut v_res_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3273_ = (crate::leanh::lean_unbox(v_t_3270_) as u8);
    v_res_3274_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim(
        v_motive_3268_,
        v_ctorIdx_3269_,
        v_t_boxed_3273_,
        v_h_3271_,
        v_k_3272_,
    );
    crate::leanh::lean_dec(v_k_3272_);
    crate::leanh::lean_dec(v_ctorIdx_3269_);
    return v_res_3274_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(
    mut v_unsolvedGoals_3275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unsolvedGoals_3275_);
    return v_unsolvedGoals_3275_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg___boxed(
    mut v_unsolvedGoals_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3277_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(v_unsolvedGoals_3276_);
    crate::leanh::lean_dec(v_unsolvedGoals_3276_);
    return v_res_3277_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(
    mut v_motive_3278_: *mut crate::leanh::LeanObject,
    mut v_t_3279_: u8,
    mut v_h_3280_: *mut crate::leanh::LeanObject,
    mut v_unsolvedGoals_3281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unsolvedGoals_3281_);
    return v_unsolvedGoals_3281_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___boxed(
    mut v_motive_3282_: *mut crate::leanh::LeanObject,
    mut v_t_3283_: *mut crate::leanh::LeanObject,
    mut v_h_3284_: *mut crate::leanh::LeanObject,
    mut v_unsolvedGoals_3285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3286_: u8 = 0;
    let mut v_res_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3286_ = (crate::leanh::lean_unbox(v_t_3283_) as u8);
    v_res_3287_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(
        v_motive_3282_,
        v_t_boxed_3286_,
        v_h_3284_,
        v_unsolvedGoals_3285_,
    );
    crate::leanh::lean_dec(v_unsolvedGoals_3285_);
    return v_res_3287_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(
    mut v_goalsAccomplished_3288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_goalsAccomplished_3288_);
    return v_goalsAccomplished_3288_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg___boxed(
    mut v_goalsAccomplished_3289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3290_ =
        l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(v_goalsAccomplished_3289_);
    crate::leanh::lean_dec(v_goalsAccomplished_3289_);
    return v_res_3290_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(
    mut v_motive_3291_: *mut crate::leanh::LeanObject,
    mut v_t_3292_: u8,
    mut v_h_3293_: *mut crate::leanh::LeanObject,
    mut v_goalsAccomplished_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_goalsAccomplished_3294_);
    return v_goalsAccomplished_3294_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___boxed(
    mut v_motive_3295_: *mut crate::leanh::LeanObject,
    mut v_t_3296_: *mut crate::leanh::LeanObject,
    mut v_h_3297_: *mut crate::leanh::LeanObject,
    mut v_goalsAccomplished_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3299_: u8 = 0;
    let mut v_res_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3299_ = (crate::leanh::lean_unbox(v_t_3296_) as u8);
    v_res_3300_ = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(
        v_motive_3295_,
        v_t_boxed_3299_,
        v_h_3297_,
        v_goalsAccomplished_3298_,
    );
    crate::leanh::lean_dec(v_goalsAccomplished_3298_);
    return v_res_3300_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default() -> u8 {
    let mut v___x_3301_: u8 = 0;
    v___x_3301_ = 0;
    return v___x_3301_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag() -> u8 {
    let mut v___x_3302_: u8 = 0;
    v___x_3302_ = 0;
    return v___x_3302_;
}
pub unsafe fn l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(mut v_x_3303_: u8, mut v_y_3304_: u8) -> u8 {
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: u8 = 0;
    v___x_3305_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_3303_);
    v___x_3306_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_y_3304_);
    v___x_3307_ = lean_nat_dec_eq(v___x_3305_, v___x_3306_);
    crate::leanh::lean_dec(v___x_3306_);
    crate::leanh::lean_dec(v___x_3305_);
    return v___x_3307_;
}
pub unsafe fn l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed(
    mut v_x_3308_: *mut crate::leanh::LeanObject,
    mut v_y_3309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_3310_: u8 = 0;
    let mut v_y_18__boxed_3311_: u8 = 0;
    let mut v_res_3312_: u8 = 0;
    let mut v_r_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_3310_ = (crate::leanh::lean_unbox(v_x_3308_) as u8);
    v_y_18__boxed_3311_ = (crate::leanh::lean_unbox(v_y_3309_) as u8);
    v_res_3312_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v_x_17__boxed_3310_, v_y_18__boxed_3311_);
    v_r_3313_ = crate::leanh::lean_box((v_res_3312_) as usize);
    return v_r_3313_;
}
pub unsafe fn l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(mut v_x_3316_: u8, mut v_y_3317_: u8) -> u8 {
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    v___x_3318_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_3316_);
    v___x_3319_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_y_3317_);
    v___x_3320_ = lean_nat_dec_lt(v___x_3318_, v___x_3319_);
    if v___x_3320_ == 0 {
        let mut v___x_3321_: u8 = 0;
        v___x_3321_ = lean_nat_dec_eq(v___x_3318_, v___x_3319_);
        crate::leanh::lean_dec(v___x_3319_);
        crate::leanh::lean_dec(v___x_3318_);
        if v___x_3321_ == 0 {
            let mut v___x_3322_: u8 = 0;
            v___x_3322_ = 2;
            return v___x_3322_;
        } else {
            let mut v___x_3323_: u8 = 0;
            v___x_3323_ = 1;
            return v___x_3323_;
        }
    } else {
        let mut v___x_3324_: u8 = 0;
        crate::leanh::lean_dec(v___x_3319_);
        crate::leanh::lean_dec(v___x_3318_);
        v___x_3324_ = 0;
        return v___x_3324_;
    }
}
pub unsafe fn l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed(
    mut v_x_3325_: *mut crate::leanh::LeanObject,
    mut v_y_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30__boxed_3327_: u8 = 0;
    let mut v_y_31__boxed_3328_: u8 = 0;
    let mut v_res_3329_: u8 = 0;
    let mut v_r_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_3327_ = (crate::leanh::lean_unbox(v_x_3325_) as u8);
    v_y_31__boxed_3328_ = (crate::leanh::lean_unbox(v_y_3326_) as u8);
    v_res_3329_ = l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(v_x_30__boxed_3327_, v_y_31__boxed_3328_);
    v_r_3330_ = crate::leanh::lean_box((v_res_3329_) as usize);
    return v_r_3330_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0(
    mut v_j_3342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: u8 = 0;
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: u8 = 0;
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3345_ = l_Lean_Json_getNat_x3f(v_j_3342_);
                if crate::leanh::lean_obj_tag(v___x_3345_) == 1 {
                    v_a_3346_ = crate::leanh::lean_ctor_get(v___x_3345_, 0);
                    crate::leanh::lean_inc(v_a_3346_);
                    crate::leanh::lean_dec_ref_known(v___x_3345_, 1);
                    v___x_3347_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3348_ = lean_nat_dec_eq(v_a_3346_, v___x_3347_);
                    if v___x_3348_ == 0 {
                        v___x_3349_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_3350_ = lean_nat_dec_eq(v_a_3346_, v___x_3349_);
                        crate::leanh::lean_dec(v_a_3346_);
                        if v___x_3350_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_3351_ =
                                l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2;
                            return v___x_3351_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3346_);
                        v___x_3352_ = l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3;
                        return v___x_3352_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3345_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3344_ = l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1;
                return v___x_3344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(
    mut v_x_3355_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_3355_ == 0 {
        let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3356_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once
            ),
            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1,
        );
        return v___x_3356_;
    } else {
        let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3357_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once
            ),
            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3,
        );
        return v___x_3357_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed(
    mut v_x_3358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_48__boxed_3359_: u8 = 0;
    let mut v_res_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_48__boxed_3359_ = (crate::leanh::lean_unbox(v_x_3358_) as u8);
    v_res_3360_ = l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(v_x_48__boxed_3359_);
    return v_res_3360_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3364_ = l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0;
    v___x_3365_ = l_Lean_Lsp_instInhabitedLocation_default;
    v___x_3366_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3366_, 0, v___x_3365_);
    crate::leanh::lean_ctor_set(v___x_3366_, 1, v___x_3364_);
    return v___x_3366_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3367_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once
        ),
        _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1,
    );
    return v___x_3367_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3368_ = l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default;
    return v___x_3368_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(
    mut v_x_3369_: *mut crate::leanh::LeanObject,
    mut v_x_3370_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_location_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_location_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: u8 = 0;
    v_location_3371_ = crate::leanh::lean_ctor_get(v_x_3369_, 0);
    v_message_3372_ = crate::leanh::lean_ctor_get(v_x_3369_, 1);
    v_location_3373_ = crate::leanh::lean_ctor_get(v_x_3370_, 0);
    v_message_3374_ = crate::leanh::lean_ctor_get(v_x_3370_, 1);
    v___x_3375_ = l_Lean_Lsp_instBEqLocation_beq(v_location_3371_, v_location_3373_);
    if v___x_3375_ == 0 {
        return v___x_3375_;
    } else {
        let mut v___x_3376_: u8 = 0;
        v___x_3376_ = lean_string_dec_eq(v_message_3372_, v_message_3374_);
        return v___x_3376_;
    }
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed(
    mut v_x_3377_: *mut crate::leanh::LeanObject,
    mut v_x_3378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3379_: u8 = 0;
    let mut v_r_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3379_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(v_x_3377_, v_x_3378_);
    crate::leanh::lean_dec_ref(v_x_3378_);
    crate::leanh::lean_dec_ref(v_x_3377_);
    v_r_3380_ = crate::leanh::lean_box((v_res_3379_) as usize);
    return v_r_3380_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(
    mut v_a_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3383_) == 0 {
                    v___x_3385_ = lean_array_to_list(v_a_3384_);
                    return v___x_3385_;
                } else {
                    v_head_3386_ = crate::leanh::lean_ctor_get(v_a_3383_, 0);
                    crate::leanh::lean_inc(v_head_3386_);
                    v_tail_3387_ = crate::leanh::lean_ctor_get(v_a_3383_, 1);
                    crate::leanh::lean_inc(v_tail_3387_);
                    crate::leanh::lean_dec_ref_known(v_a_3383_, 2);
                    v___x_3388_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_3384_,
                        v_head_3386_,
                    );
                    v_a_3383_ = v_tail_3387_;
                    v_a_3384_ = v___x_3388_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(
    mut v_x_3394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_location_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3399_: u8 = 0;
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_location_3395_ = crate::leanh::lean_ctor_get(v_x_3394_, 0);
                v_message_3396_ = crate::leanh::lean_ctor_get(v_x_3394_, 1);
                v_isSharedCheck_3416_ = (!crate::leanh::lean_is_exclusive(v_x_3394_)) as u8;
                if v_isSharedCheck_3416_ == 0 {
                    v___x_3398_ = v_x_3394_;
                    v_isShared_3399_ = v_isSharedCheck_3416_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_message_3396_);
                    crate::leanh::lean_inc(v_location_3395_);
                    crate::leanh::lean_dec(v_x_3394_);
                    v___x_3398_ = crate::leanh::lean_box(0);
                    v_isShared_3399_ = v_isSharedCheck_3416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3400_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0;
                v___x_3401_ = l_Lean_Lsp_instToJsonLocation_toJson(v_location_3395_);
                if v_isShared_3399_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3398_, 1, v___x_3401_);
                    crate::leanh::lean_ctor_set(v___x_3398_, 0, v___x_3400_);
                    v___x_3403_ = v___x_3398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3415_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3415_, 1, v___x_3401_);
                    v___x_3403_ = v_reuseFailAlloc_3415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3404_ = crate::leanh::lean_box(0);
                v___x_3405_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3405_, 0, v___x_3403_);
                crate::leanh::lean_ctor_set(v___x_3405_, 1, v___x_3404_);
                v___x_3406_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
                v___x_3407_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3407_, 0, v_message_3396_);
                v___x_3408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3408_, 0, v___x_3406_);
                crate::leanh::lean_ctor_set(v___x_3408_, 1, v___x_3407_);
                v___x_3409_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3409_, 0, v___x_3408_);
                crate::leanh::lean_ctor_set(v___x_3409_, 1, v___x_3404_);
                v___x_3410_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3410_, 0, v___x_3409_);
                crate::leanh::lean_ctor_set(v___x_3410_, 1, v___x_3404_);
                v___x_3411_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3411_, 0, v___x_3405_);
                crate::leanh::lean_ctor_set(v___x_3411_, 1, v___x_3410_);
                v___x_3412_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2;
                v___x_3413_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_3411_, v___x_3412_);
                v___x_3414_ = l_Lean_Json_mkObj(v___x_3413_);
                crate::leanh::lean_dec(v___x_3413_);
                return v___x_3414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(
    mut v_j_3419_: *mut crate::leanh::LeanObject,
    mut v_k_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ = l_Lean_Json_getObjValD(v_j_3419_, v_k_3420_);
    v___x_3422_ = l_Lean_Lsp_instFromJsonLocation_fromJson(v___x_3421_);
    return v___x_3422_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0___boxed(
    mut v_j_3423_: *mut crate::leanh::LeanObject,
    mut v_k_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_j_3423_, v_k_3424_);
    crate::leanh::lean_dec_ref(v_k_3424_);
    return v_res_3425_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(
    mut v_j_3426_: *mut crate::leanh::LeanObject,
    mut v_k_3427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3428_ = l_Lean_Json_getObjValD(v_j_3426_, v_k_3427_);
    v___x_3429_ = l_Lean_Json_getStr_x3f(v___x_3428_);
    return v___x_3429_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1___boxed(
    mut v_j_3430_: *mut crate::leanh::LeanObject,
    mut v_k_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_j_3430_, v_k_3431_);
    crate::leanh::lean_dec_ref(v_k_3431_);
    return v_res_3432_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3440_: u8 = 0;
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3440_ = 1;
    v___x_3441_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3;
    v___x_3442_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3441_, v___x_3440_);
    return v___x_3442_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3444_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5;
    v___x_3445_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4,
    );
    v___x_3446_ = lean_string_append(v___x_3445_, v___x_3444_);
    return v___x_3446_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3449_ = 1;
    v___x_3450_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7;
    v___x_3451_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3450_, v___x_3449_);
    return v___x_3451_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3452_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8,
    );
    v___x_3453_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6,
    );
    v___x_3454_ = lean_string_append(v___x_3453_, v___x_3452_);
    return v___x_3454_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3457_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9,
    );
    v___x_3458_ = lean_string_append(v___x_3457_, v___x_3456_);
    return v___x_3458_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3461_ = 1;
    v___x_3462_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12;
    v___x_3463_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3462_, v___x_3461_);
    return v___x_3463_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3464_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13,
    );
    v___x_3465_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6,
    );
    v___x_3466_ = lean_string_append(v___x_3465_, v___x_3464_);
    return v___x_3466_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3467_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3468_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14,
    );
    v___x_3469_ = lean_string_append(v___x_3468_, v___x_3467_);
    return v___x_3469_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(
    mut v_json_3470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut v_a_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3490_: u8 = 0;
    let mut v_a_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3497_: u8 = 0;
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3503_: u8 = 0;
    let mut v_a_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3507_: u8 = 0;
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3511_: u8 = 0;
    let mut v_a_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3471_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0;
                crate::leanh::lean_inc(v_json_3470_);
                v___x_3472_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_json_3470_, v___x_3471_);
                if crate::leanh::lean_obj_tag(v___x_3472_) == 0 {
                    crate::leanh::lean_dec(v_json_3470_);
                    v_a_3473_ = crate::leanh::lean_ctor_get(v___x_3472_, 0);
                    v_isSharedCheck_3482_ = (!crate::leanh::lean_is_exclusive(v___x_3472_)) as u8;
                    if v_isSharedCheck_3482_ == 0 {
                        v___x_3475_ = v___x_3472_;
                        v_isShared_3476_ = v_isSharedCheck_3482_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3473_);
                        crate::leanh::lean_dec(v___x_3472_);
                        v___x_3475_ = crate::leanh::lean_box(0);
                        v_isShared_3476_ = v_isSharedCheck_3482_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3472_) == 0 {
                        crate::leanh::lean_dec(v_json_3470_);
                        v_a_3483_ = crate::leanh::lean_ctor_get(v___x_3472_, 0);
                        v_isSharedCheck_3490_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3472_)) as u8;
                        if v_isSharedCheck_3490_ == 0 {
                            v___x_3485_ = v___x_3472_;
                            v_isShared_3486_ = v_isSharedCheck_3490_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3483_);
                            crate::leanh::lean_dec(v___x_3472_);
                            v___x_3485_ = crate::leanh::lean_box(0);
                            v_isShared_3486_ = v_isSharedCheck_3490_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3491_ = crate::leanh::lean_ctor_get(v___x_3472_, 0);
                        crate::leanh::lean_inc(v_a_3491_);
                        crate::leanh::lean_dec_ref_known(v___x_3472_, 1);
                        v___x_3492_ =
                            l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
                        v___x_3493_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_3470_, v___x_3492_);
                        if crate::leanh::lean_obj_tag(v___x_3493_) == 0 {
                            crate::leanh::lean_dec(v_a_3491_);
                            v_a_3494_ = crate::leanh::lean_ctor_get(v___x_3493_, 0);
                            v_isSharedCheck_3503_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3493_)) as u8;
                            if v_isSharedCheck_3503_ == 0 {
                                v___x_3496_ = v___x_3493_;
                                v_isShared_3497_ = v_isSharedCheck_3503_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3494_);
                                crate::leanh::lean_dec(v___x_3493_);
                                v___x_3496_ = crate::leanh::lean_box(0);
                                v_isShared_3497_ = v_isSharedCheck_3503_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_3493_) == 0 {
                                crate::leanh::lean_dec(v_a_3491_);
                                v_a_3504_ = crate::leanh::lean_ctor_get(v___x_3493_, 0);
                                v_isSharedCheck_3511_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3493_)) as u8;
                                if v_isSharedCheck_3511_ == 0 {
                                    v___x_3506_ = v___x_3493_;
                                    v_isShared_3507_ = v_isSharedCheck_3511_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3504_);
                                    crate::leanh::lean_dec(v___x_3493_);
                                    v___x_3506_ = crate::leanh::lean_box(0);
                                    v_isShared_3507_ = v_isSharedCheck_3511_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3512_ = crate::leanh::lean_ctor_get(v___x_3493_, 0);
                                v_isSharedCheck_3520_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3493_)) as u8;
                                if v_isSharedCheck_3520_ == 0 {
                                    v___x_3514_ = v___x_3493_;
                                    v_isShared_3515_ = v_isSharedCheck_3520_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3512_);
                                    crate::leanh::lean_dec(v___x_3493_);
                                    v___x_3514_ = crate::leanh::lean_box(0);
                                    v_isShared_3515_ = v_isSharedCheck_3520_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3477_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once), _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11);
                v___x_3478_ = lean_string_append(v___x_3477_, v_a_3473_);
                crate::leanh::lean_dec(v_a_3473_);
                if v_isShared_3476_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3475_, 0, v___x_3478_);
                    v___x_3480_ = v___x_3475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
                    v___x_3480_ = v_reuseFailAlloc_3481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3480_;
            }
            3 => {
                if v_isShared_3486_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3485_, 0);
                    v___x_3488_ = v___x_3485_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3489_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
                    v___x_3488_ = v_reuseFailAlloc_3489_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3488_;
            }
            5 => {
                v___x_3498_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once), _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15);
                v___x_3499_ = lean_string_append(v___x_3498_, v_a_3494_);
                crate::leanh::lean_dec(v_a_3494_);
                if v_isShared_3497_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3496_, 0, v___x_3499_);
                    v___x_3501_ = v___x_3496_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
                    v___x_3501_ = v_reuseFailAlloc_3502_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3501_;
            }
            7 => {
                if v_isShared_3507_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3506_, 0);
                    v___x_3509_ = v___x_3506_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
                    v___x_3509_ = v_reuseFailAlloc_3510_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3509_;
            }
            9 => {
                v___x_3516_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3516_, 0, v_a_3491_);
                crate::leanh::lean_ctor_set(v___x_3516_, 1, v_a_3512_);
                if v_isShared_3515_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3514_, 0, v___x_3516_);
                    v___x_3518_ = v___x_3514_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
                    v___x_3518_ = v_reuseFailAlloc_3519_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(
    mut v_x_3523_: *mut crate::leanh::LeanObject,
    mut v_x_3524_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_location_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_location_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    v_location_3525_ = crate::leanh::lean_ctor_get(v_x_3523_, 0);
    v_message_3526_ = crate::leanh::lean_ctor_get(v_x_3523_, 1);
    v_location_3527_ = crate::leanh::lean_ctor_get(v_x_3524_, 0);
    v_message_3528_ = crate::leanh::lean_ctor_get(v_x_3524_, 1);
    v___x_3529_ = l_Lean_Lsp_instOrdLocation_ord(v_location_3525_, v_location_3527_);
    if v___x_3529_ == 1 {
        let mut v___x_3530_: u8 = 0;
        v___x_3530_ = lean_string_compare(v_message_3526_, v_message_3528_);
        if v___x_3530_ == 1 {
            return v___x_3530_;
        } else {
            return v___x_3530_;
        }
    } else {
        return v___x_3529_;
    }
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed(
    mut v_x_3531_: *mut crate::leanh::LeanObject,
    mut v_x_3532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3533_: u8 = 0;
    let mut v_r_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3533_ = l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(v_x_3531_, v_x_3532_);
    crate::leanh::lean_dec_ref(v_x_3532_);
    crate::leanh::lean_dec_ref(v_x_3531_);
    v_r_3534_ = crate::leanh::lean_box((v_res_3533_) as usize);
    return v_r_3534_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3537_ = l_Lean_Lsp_instInhabitedRange_default;
    v___x_3538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3538_, 0, v___x_3537_);
    return v___x_3538_;
}
pub unsafe fn l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(
    mut v_inst_3539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3540_ = l_Lean_Lsp_instInhabitedRange_default;
    v___x_3541_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once
        ),
        _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0,
    );
    v___x_3542_ = crate::leanh::lean_box(0);
    v___x_3543_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3543_, 0, v___x_3540_);
    crate::leanh::lean_ctor_set(v___x_3543_, 1, v___x_3541_);
    crate::leanh::lean_ctor_set(v___x_3543_, 2, v___x_3542_);
    crate::leanh::lean_ctor_set(v___x_3543_, 3, v___x_3542_);
    crate::leanh::lean_ctor_set(v___x_3543_, 4, v___x_3542_);
    crate::leanh::lean_ctor_set(v___x_3543_, 5, v___x_3542_);
    crate::leanh::lean_ctor_set(v___x_3543_, 6, v_inst_3539_);
    crate::leanh::lean_ctor_set(v___x_3543_, 7, v___x_3542_);
    crate::leanh::lean_ctor_set(v___x_3543_, 8, v___x_3542_);
    crate::leanh::lean_ctor_set(v___x_3543_, 9, v___x_3542_);
    crate::leanh::lean_ctor_set(v___x_3543_, 10, v___x_3542_);
    return v___x_3543_;
}
pub unsafe fn l_Lean_Lsp_instInhabitedDiagnosticWith_default(
    mut v_00_u03b1_3544_: *mut crate::leanh::LeanObject,
    mut v_inst_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3546_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_3545_);
    return v___x_3546_;
}
pub unsafe fn l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(
    mut v_inst_3547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3548_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_3547_);
    return v___x_3548_;
}
pub unsafe fn l_Lean_Lsp_instInhabitedDiagnosticWith(
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_inst_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3551_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_3550_);
    return v___x_3551_;
}
pub unsafe fn _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqBool___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_3554_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3554_, 0, v___x_3553_);
    return v___f_3554_;
}
pub unsafe fn _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3555_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqString___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_3556_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3556_, 0, v___x_3555_);
    return v___f_3556_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(
    mut v_inst_3564_: *mut crate::leanh::LeanObject,
    mut v_x_3565_: *mut crate::leanh::LeanObject,
    mut v_x_3566_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_range_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: u8 = 0;
    v_range_3567_ = crate::leanh::lean_ctor_get(v_x_3565_, 0);
    crate::leanh::lean_inc_ref(v_range_3567_);
    v_fullRange_x3f_3568_ = crate::leanh::lean_ctor_get(v_x_3565_, 1);
    crate::leanh::lean_inc(v_fullRange_x3f_3568_);
    v_severity_x3f_3569_ = crate::leanh::lean_ctor_get(v_x_3565_, 2);
    crate::leanh::lean_inc(v_severity_x3f_3569_);
    v_isSilent_x3f_3570_ = crate::leanh::lean_ctor_get(v_x_3565_, 3);
    crate::leanh::lean_inc(v_isSilent_x3f_3570_);
    v_code_x3f_3571_ = crate::leanh::lean_ctor_get(v_x_3565_, 4);
    crate::leanh::lean_inc(v_code_x3f_3571_);
    v_source_x3f_3572_ = crate::leanh::lean_ctor_get(v_x_3565_, 5);
    crate::leanh::lean_inc(v_source_x3f_3572_);
    v_message_3573_ = crate::leanh::lean_ctor_get(v_x_3565_, 6);
    crate::leanh::lean_inc(v_message_3573_);
    v_tags_x3f_3574_ = crate::leanh::lean_ctor_get(v_x_3565_, 7);
    crate::leanh::lean_inc(v_tags_x3f_3574_);
    v_leanTags_x3f_3575_ = crate::leanh::lean_ctor_get(v_x_3565_, 8);
    crate::leanh::lean_inc(v_leanTags_x3f_3575_);
    v_relatedInformation_x3f_3576_ = crate::leanh::lean_ctor_get(v_x_3565_, 9);
    crate::leanh::lean_inc(v_relatedInformation_x3f_3576_);
    v_data_x3f_3577_ = crate::leanh::lean_ctor_get(v_x_3565_, 10);
    crate::leanh::lean_inc(v_data_x3f_3577_);
    crate::leanh::lean_dec_ref(v_x_3565_);
    v_range_3578_ = crate::leanh::lean_ctor_get(v_x_3566_, 0);
    crate::leanh::lean_inc_ref(v_range_3578_);
    v_fullRange_x3f_3579_ = crate::leanh::lean_ctor_get(v_x_3566_, 1);
    crate::leanh::lean_inc(v_fullRange_x3f_3579_);
    v_severity_x3f_3580_ = crate::leanh::lean_ctor_get(v_x_3566_, 2);
    crate::leanh::lean_inc(v_severity_x3f_3580_);
    v_isSilent_x3f_3581_ = crate::leanh::lean_ctor_get(v_x_3566_, 3);
    crate::leanh::lean_inc(v_isSilent_x3f_3581_);
    v_code_x3f_3582_ = crate::leanh::lean_ctor_get(v_x_3566_, 4);
    crate::leanh::lean_inc(v_code_x3f_3582_);
    v_source_x3f_3583_ = crate::leanh::lean_ctor_get(v_x_3566_, 5);
    crate::leanh::lean_inc(v_source_x3f_3583_);
    v_message_3584_ = crate::leanh::lean_ctor_get(v_x_3566_, 6);
    crate::leanh::lean_inc(v_message_3584_);
    v_tags_x3f_3585_ = crate::leanh::lean_ctor_get(v_x_3566_, 7);
    crate::leanh::lean_inc(v_tags_x3f_3585_);
    v_leanTags_x3f_3586_ = crate::leanh::lean_ctor_get(v_x_3566_, 8);
    crate::leanh::lean_inc(v_leanTags_x3f_3586_);
    v_relatedInformation_x3f_3587_ = crate::leanh::lean_ctor_get(v_x_3566_, 9);
    crate::leanh::lean_inc(v_relatedInformation_x3f_3587_);
    v_data_x3f_3588_ = crate::leanh::lean_ctor_get(v_x_3566_, 10);
    crate::leanh::lean_inc(v_data_x3f_3588_);
    crate::leanh::lean_dec_ref(v_x_3566_);
    v___x_3589_ = l_Lean_Lsp_instBEqRange_beq(v_range_3567_, v_range_3578_);
    crate::leanh::lean_dec_ref(v_range_3578_);
    crate::leanh::lean_dec_ref(v_range_3567_);
    if v___x_3589_ == 0 {
        crate::leanh::lean_dec(v_data_x3f_3588_);
        crate::leanh::lean_dec(v_relatedInformation_x3f_3587_);
        crate::leanh::lean_dec(v_leanTags_x3f_3586_);
        crate::leanh::lean_dec(v_tags_x3f_3585_);
        crate::leanh::lean_dec(v_message_3584_);
        crate::leanh::lean_dec(v_source_x3f_3583_);
        crate::leanh::lean_dec(v_code_x3f_3582_);
        crate::leanh::lean_dec(v_isSilent_x3f_3581_);
        crate::leanh::lean_dec(v_severity_x3f_3580_);
        crate::leanh::lean_dec(v_fullRange_x3f_3579_);
        crate::leanh::lean_dec(v_data_x3f_3577_);
        crate::leanh::lean_dec(v_relatedInformation_x3f_3576_);
        crate::leanh::lean_dec(v_leanTags_x3f_3575_);
        crate::leanh::lean_dec(v_tags_x3f_3574_);
        crate::leanh::lean_dec(v_message_3573_);
        crate::leanh::lean_dec(v_source_x3f_3572_);
        crate::leanh::lean_dec(v_code_x3f_3571_);
        crate::leanh::lean_dec(v_isSilent_x3f_3570_);
        crate::leanh::lean_dec(v_severity_x3f_3569_);
        crate::leanh::lean_dec(v_fullRange_x3f_3568_);
        crate::leanh::lean_dec_ref(v_inst_3564_);
        return v___x_3589_;
    } else {
        let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3591_: u8 = 0;
        v___x_3590_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0;
        v___x_3591_ = l_Option_instBEq_beq___redArg(
            v___x_3590_,
            v_fullRange_x3f_3568_,
            v_fullRange_x3f_3579_,
        );
        if v___x_3591_ == 0 {
            crate::leanh::lean_dec(v_data_x3f_3588_);
            crate::leanh::lean_dec(v_relatedInformation_x3f_3587_);
            crate::leanh::lean_dec(v_leanTags_x3f_3586_);
            crate::leanh::lean_dec(v_tags_x3f_3585_);
            crate::leanh::lean_dec(v_message_3584_);
            crate::leanh::lean_dec(v_source_x3f_3583_);
            crate::leanh::lean_dec(v_code_x3f_3582_);
            crate::leanh::lean_dec(v_isSilent_x3f_3581_);
            crate::leanh::lean_dec(v_severity_x3f_3580_);
            crate::leanh::lean_dec(v_data_x3f_3577_);
            crate::leanh::lean_dec(v_relatedInformation_x3f_3576_);
            crate::leanh::lean_dec(v_leanTags_x3f_3575_);
            crate::leanh::lean_dec(v_tags_x3f_3574_);
            crate::leanh::lean_dec(v_message_3573_);
            crate::leanh::lean_dec(v_source_x3f_3572_);
            crate::leanh::lean_dec(v_code_x3f_3571_);
            crate::leanh::lean_dec(v_isSilent_x3f_3570_);
            crate::leanh::lean_dec(v_severity_x3f_3569_);
            crate::leanh::lean_dec_ref(v_inst_3564_);
            return v___x_3591_;
        } else {
            let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3593_: u8 = 0;
            v___x_3592_ = l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0;
            v___x_3593_ = l_Option_instBEq_beq___redArg(
                v___x_3592_,
                v_severity_x3f_3569_,
                v_severity_x3f_3580_,
            );
            if v___x_3593_ == 0 {
                crate::leanh::lean_dec(v_data_x3f_3588_);
                crate::leanh::lean_dec(v_relatedInformation_x3f_3587_);
                crate::leanh::lean_dec(v_leanTags_x3f_3586_);
                crate::leanh::lean_dec(v_tags_x3f_3585_);
                crate::leanh::lean_dec(v_message_3584_);
                crate::leanh::lean_dec(v_source_x3f_3583_);
                crate::leanh::lean_dec(v_code_x3f_3582_);
                crate::leanh::lean_dec(v_isSilent_x3f_3581_);
                crate::leanh::lean_dec(v_data_x3f_3577_);
                crate::leanh::lean_dec(v_relatedInformation_x3f_3576_);
                crate::leanh::lean_dec(v_leanTags_x3f_3575_);
                crate::leanh::lean_dec(v_tags_x3f_3574_);
                crate::leanh::lean_dec(v_message_3573_);
                crate::leanh::lean_dec(v_source_x3f_3572_);
                crate::leanh::lean_dec(v_code_x3f_3571_);
                crate::leanh::lean_dec(v_isSilent_x3f_3570_);
                crate::leanh::lean_dec_ref(v_inst_3564_);
                return v___x_3593_;
            } else {
                let mut v___f_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3595_: u8 = 0;
                v___f_3594_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_once
                    ),
                    _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1,
                );
                v___x_3595_ = l_Option_instBEq_beq___redArg(
                    v___f_3594_,
                    v_isSilent_x3f_3570_,
                    v_isSilent_x3f_3581_,
                );
                if v___x_3595_ == 0 {
                    crate::leanh::lean_dec(v_data_x3f_3588_);
                    crate::leanh::lean_dec(v_relatedInformation_x3f_3587_);
                    crate::leanh::lean_dec(v_leanTags_x3f_3586_);
                    crate::leanh::lean_dec(v_tags_x3f_3585_);
                    crate::leanh::lean_dec(v_message_3584_);
                    crate::leanh::lean_dec(v_source_x3f_3583_);
                    crate::leanh::lean_dec(v_code_x3f_3582_);
                    crate::leanh::lean_dec(v_data_x3f_3577_);
                    crate::leanh::lean_dec(v_relatedInformation_x3f_3576_);
                    crate::leanh::lean_dec(v_leanTags_x3f_3575_);
                    crate::leanh::lean_dec(v_tags_x3f_3574_);
                    crate::leanh::lean_dec(v_message_3573_);
                    crate::leanh::lean_dec(v_source_x3f_3572_);
                    crate::leanh::lean_dec(v_code_x3f_3571_);
                    crate::leanh::lean_dec_ref(v_inst_3564_);
                    return v___x_3595_;
                } else {
                    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3597_: u8 = 0;
                    v___x_3596_ = l_Lean_Lsp_instBEqDiagnosticCode___closed__0;
                    v___x_3597_ = l_Option_instBEq_beq___redArg(
                        v___x_3596_,
                        v_code_x3f_3571_,
                        v_code_x3f_3582_,
                    );
                    if v___x_3597_ == 0 {
                        crate::leanh::lean_dec(v_data_x3f_3588_);
                        crate::leanh::lean_dec(v_relatedInformation_x3f_3587_);
                        crate::leanh::lean_dec(v_leanTags_x3f_3586_);
                        crate::leanh::lean_dec(v_tags_x3f_3585_);
                        crate::leanh::lean_dec(v_message_3584_);
                        crate::leanh::lean_dec(v_source_x3f_3583_);
                        crate::leanh::lean_dec(v_data_x3f_3577_);
                        crate::leanh::lean_dec(v_relatedInformation_x3f_3576_);
                        crate::leanh::lean_dec(v_leanTags_x3f_3575_);
                        crate::leanh::lean_dec(v_tags_x3f_3574_);
                        crate::leanh::lean_dec(v_message_3573_);
                        crate::leanh::lean_dec(v_source_x3f_3572_);
                        crate::leanh::lean_dec_ref(v_inst_3564_);
                        return v___x_3597_;
                    } else {
                        let mut v___f_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3599_: u8 = 0;
                        v___f_3598_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_once
                            ),
                            _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2,
                        );
                        v___x_3599_ = l_Option_instBEq_beq___redArg(
                            v___f_3598_,
                            v_source_x3f_3572_,
                            v_source_x3f_3583_,
                        );
                        if v___x_3599_ == 0 {
                            crate::leanh::lean_dec(v_data_x3f_3588_);
                            crate::leanh::lean_dec(v_relatedInformation_x3f_3587_);
                            crate::leanh::lean_dec(v_leanTags_x3f_3586_);
                            crate::leanh::lean_dec(v_tags_x3f_3585_);
                            crate::leanh::lean_dec(v_message_3584_);
                            crate::leanh::lean_dec(v_data_x3f_3577_);
                            crate::leanh::lean_dec(v_relatedInformation_x3f_3576_);
                            crate::leanh::lean_dec(v_leanTags_x3f_3575_);
                            crate::leanh::lean_dec(v_tags_x3f_3574_);
                            crate::leanh::lean_dec(v_message_3573_);
                            crate::leanh::lean_dec_ref(v_inst_3564_);
                            return v___x_3599_;
                        } else {
                            let mut v___x_3600_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3601_: u8 = 0;
                            v___x_3600_ = crate::leanh::lean_apply_2(
                                v_inst_3564_,
                                v_message_3573_,
                                v_message_3584_,
                            );
                            v___x_3601_ = (crate::leanh::lean_unbox(v___x_3600_) as u8);
                            if v___x_3601_ == 0 {
                                let mut v___x_3602_: u8 = 0;
                                crate::leanh::lean_dec(v_data_x3f_3588_);
                                crate::leanh::lean_dec(v_relatedInformation_x3f_3587_);
                                crate::leanh::lean_dec(v_leanTags_x3f_3586_);
                                crate::leanh::lean_dec(v_tags_x3f_3585_);
                                crate::leanh::lean_dec(v_data_x3f_3577_);
                                crate::leanh::lean_dec(v_relatedInformation_x3f_3576_);
                                crate::leanh::lean_dec(v_leanTags_x3f_3575_);
                                crate::leanh::lean_dec(v_tags_x3f_3574_);
                                v___x_3602_ = (crate::leanh::lean_unbox(v___x_3600_) as u8);
                                return v___x_3602_;
                            } else {
                                let mut v___f_3603_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3604_: u8 = 0;
                                v___f_3603_ =
                                    l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3;
                                v___x_3604_ = l_Option_instBEq_beq___redArg(
                                    v___f_3603_,
                                    v_tags_x3f_3574_,
                                    v_tags_x3f_3585_,
                                );
                                if v___x_3604_ == 0 {
                                    crate::leanh::lean_dec(v_data_x3f_3588_);
                                    crate::leanh::lean_dec(v_relatedInformation_x3f_3587_);
                                    crate::leanh::lean_dec(v_leanTags_x3f_3586_);
                                    crate::leanh::lean_dec(v_data_x3f_3577_);
                                    crate::leanh::lean_dec(v_relatedInformation_x3f_3576_);
                                    crate::leanh::lean_dec(v_leanTags_x3f_3575_);
                                    return v___x_3604_;
                                } else {
                                    let mut v___f_3605_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3606_: u8 = 0;
                                    v___f_3605_ =
                                        l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4;
                                    v___x_3606_ = l_Option_instBEq_beq___redArg(
                                        v___f_3605_,
                                        v_leanTags_x3f_3575_,
                                        v_leanTags_x3f_3586_,
                                    );
                                    if v___x_3606_ == 0 {
                                        crate::leanh::lean_dec(v_data_x3f_3588_);
                                        crate::leanh::lean_dec(v_relatedInformation_x3f_3587_);
                                        crate::leanh::lean_dec(v_data_x3f_3577_);
                                        crate::leanh::lean_dec(v_relatedInformation_x3f_3576_);
                                        return v___x_3606_;
                                    } else {
                                        let mut v___f_3607_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3608_: u8 = 0;
                                        v___f_3607_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5;
                                        v___x_3608_ = l_Option_instBEq_beq___redArg(
                                            v___f_3607_,
                                            v_relatedInformation_x3f_3576_,
                                            v_relatedInformation_x3f_3587_,
                                        );
                                        if v___x_3608_ == 0 {
                                            crate::leanh::lean_dec(v_data_x3f_3588_);
                                            crate::leanh::lean_dec(v_data_x3f_3577_);
                                            return v___x_3608_;
                                        } else {
                                            let mut v___x_3609_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3610_: u8 = 0;
                                            v___x_3609_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6;
                                            v___x_3610_ = l_Option_instBEq_beq___redArg(
                                                v___x_3609_,
                                                v_data_x3f_3577_,
                                                v_data_x3f_3588_,
                                            );
                                            return v___x_3610_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___boxed(
    mut v_inst_3611_: *mut crate::leanh::LeanObject,
    mut v_x_3612_: *mut crate::leanh::LeanObject,
    mut v_x_3613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3614_: u8 = 0;
    let mut v_r_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3614_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_3611_, v_x_3612_, v_x_3613_);
    v_r_3615_ = crate::leanh::lean_box((v_res_3614_) as usize);
    return v_r_3615_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq(
    mut v_00_u03b1_3616_: *mut crate::leanh::LeanObject,
    mut v_inst_3617_: *mut crate::leanh::LeanObject,
    mut v_x_3618_: *mut crate::leanh::LeanObject,
    mut v_x_3619_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3620_: u8 = 0;
    v___x_3620_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_3617_, v_x_3618_, v_x_3619_);
    return v___x_3620_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(
    mut v_00_u03b1_3621_: *mut crate::leanh::LeanObject,
    mut v_inst_3622_: *mut crate::leanh::LeanObject,
    mut v_x_3623_: *mut crate::leanh::LeanObject,
    mut v_x_3624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3625_: u8 = 0;
    let mut v_r_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3625_ =
        l_Lean_Lsp_instBEqDiagnosticWith_beq(v_00_u03b1_3621_, v_inst_3622_, v_x_3623_, v_x_3624_);
    v_r_3626_ = crate::leanh::lean_box((v_res_3625_) as usize);
    return v_r_3626_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith___redArg(
    mut v_inst_3627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3628_ = crate::leanh::lean_alloc_closure(
        l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3628_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3628_, 1, v_inst_3627_);
    return v___x_3628_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith(
    mut v_00_u03b1_3629_: *mut crate::leanh::LeanObject,
    mut v_inst_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3631_ = crate::leanh::lean_alloc_closure(
        l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3631_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3631_, 1, v_inst_3630_);
    return v___x_3631_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(
    mut v_inst_3652_: *mut crate::leanh::LeanObject,
    mut v_x_3653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_3654_ = crate::leanh::lean_ctor_get(v_x_3653_, 0);
    crate::leanh::lean_inc_ref(v_range_3654_);
    v_fullRange_x3f_3655_ = crate::leanh::lean_ctor_get(v_x_3653_, 1);
    crate::leanh::lean_inc(v_fullRange_x3f_3655_);
    v_severity_x3f_3656_ = crate::leanh::lean_ctor_get(v_x_3653_, 2);
    crate::leanh::lean_inc(v_severity_x3f_3656_);
    v_isSilent_x3f_3657_ = crate::leanh::lean_ctor_get(v_x_3653_, 3);
    crate::leanh::lean_inc(v_isSilent_x3f_3657_);
    v_code_x3f_3658_ = crate::leanh::lean_ctor_get(v_x_3653_, 4);
    crate::leanh::lean_inc(v_code_x3f_3658_);
    v_source_x3f_3659_ = crate::leanh::lean_ctor_get(v_x_3653_, 5);
    crate::leanh::lean_inc(v_source_x3f_3659_);
    v_message_3660_ = crate::leanh::lean_ctor_get(v_x_3653_, 6);
    crate::leanh::lean_inc(v_message_3660_);
    v_tags_x3f_3661_ = crate::leanh::lean_ctor_get(v_x_3653_, 7);
    crate::leanh::lean_inc(v_tags_x3f_3661_);
    v_leanTags_x3f_3662_ = crate::leanh::lean_ctor_get(v_x_3653_, 8);
    crate::leanh::lean_inc(v_leanTags_x3f_3662_);
    v_relatedInformation_x3f_3663_ = crate::leanh::lean_ctor_get(v_x_3653_, 9);
    crate::leanh::lean_inc(v_relatedInformation_x3f_3663_);
    v_data_x3f_3664_ = crate::leanh::lean_ctor_get(v_x_3653_, 10);
    crate::leanh::lean_inc(v_data_x3f_3664_);
    crate::leanh::lean_dec_ref(v_x_3653_);
    v___x_3665_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0;
    v___f_3666_ = l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0;
    v___f_3667_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1;
    v___f_3668_ = l_Lean_Lsp_instToJsonDiagnosticCode___closed__0;
    v___f_3669_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2;
    v___x_3670_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3;
    v___x_3671_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4;
    v___x_3672_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5;
    v___x_3673_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6;
    v___x_3674_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7;
    v___x_3675_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_3654_);
    v___x_3676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3676_, 0, v___x_3674_);
    crate::leanh::lean_ctor_set(v___x_3676_, 1, v___x_3675_);
    v___x_3677_ = crate::leanh::lean_box(0);
    v___x_3678_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3678_, 0, v___x_3676_);
    crate::leanh::lean_ctor_set(v___x_3678_, 1, v___x_3677_);
    v___x_3679_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8;
    v___x_3680_ = l_Lean_Json_opt___redArg(v___x_3665_, v___x_3679_, v_fullRange_x3f_3655_);
    v___x_3681_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9;
    v___x_3682_ = l_Lean_Json_opt___redArg(v___f_3666_, v___x_3681_, v_severity_x3f_3656_);
    v___x_3683_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10;
    v___x_3684_ = l_Lean_Json_opt___redArg(v___f_3667_, v___x_3683_, v_isSilent_x3f_3657_);
    v___x_3685_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11;
    v___x_3686_ = l_Lean_Json_opt___redArg(v___f_3668_, v___x_3685_, v_code_x3f_3658_);
    v___x_3687_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12;
    v___x_3688_ = l_Lean_Json_opt___redArg(v___f_3669_, v___x_3687_, v_source_x3f_3659_);
    v___x_3689_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
    v___x_3690_ = crate::leanh::lean_apply_1(v_inst_3652_, v_message_3660_);
    v___x_3691_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3691_, 0, v___x_3689_);
    crate::leanh::lean_ctor_set(v___x_3691_, 1, v___x_3690_);
    v___x_3692_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3692_, 0, v___x_3691_);
    crate::leanh::lean_ctor_set(v___x_3692_, 1, v___x_3677_);
    v___x_3693_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13;
    v___x_3694_ = l_Lean_Json_opt___redArg(v___x_3670_, v___x_3693_, v_tags_x3f_3661_);
    v___x_3695_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14;
    v___x_3696_ = l_Lean_Json_opt___redArg(v___x_3671_, v___x_3695_, v_leanTags_x3f_3662_);
    v___x_3697_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15;
    v___x_3698_ =
        l_Lean_Json_opt___redArg(v___x_3672_, v___x_3697_, v_relatedInformation_x3f_3663_);
    v___x_3699_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16;
    v___x_3700_ = l_Lean_Json_opt___redArg(v___x_3673_, v___x_3699_, v_data_x3f_3664_);
    v___x_3701_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3701_, 0, v___x_3700_);
    crate::leanh::lean_ctor_set(v___x_3701_, 1, v___x_3677_);
    v___x_3702_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3702_, 0, v___x_3698_);
    crate::leanh::lean_ctor_set(v___x_3702_, 1, v___x_3701_);
    v___x_3703_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3703_, 0, v___x_3696_);
    crate::leanh::lean_ctor_set(v___x_3703_, 1, v___x_3702_);
    v___x_3704_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3704_, 0, v___x_3694_);
    crate::leanh::lean_ctor_set(v___x_3704_, 1, v___x_3703_);
    v___x_3705_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3705_, 0, v___x_3692_);
    crate::leanh::lean_ctor_set(v___x_3705_, 1, v___x_3704_);
    v___x_3706_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3706_, 0, v___x_3688_);
    crate::leanh::lean_ctor_set(v___x_3706_, 1, v___x_3705_);
    v___x_3707_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3707_, 0, v___x_3686_);
    crate::leanh::lean_ctor_set(v___x_3707_, 1, v___x_3706_);
    v___x_3708_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3708_, 0, v___x_3684_);
    crate::leanh::lean_ctor_set(v___x_3708_, 1, v___x_3707_);
    v___x_3709_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3709_, 0, v___x_3682_);
    crate::leanh::lean_ctor_set(v___x_3709_, 1, v___x_3708_);
    v___x_3710_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3710_, 0, v___x_3680_);
    crate::leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
    v___x_3711_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3711_, 0, v___x_3678_);
    crate::leanh::lean_ctor_set(v___x_3711_, 1, v___x_3710_);
    v___x_3712_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2;
    v___x_3713_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3673_,
        v___x_3711_,
        v___x_3712_,
    );
    v___x_3714_ = l_Lean_Json_mkObj(v___x_3713_);
    crate::leanh::lean_dec(v___x_3713_);
    return v___x_3714_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith_toJson(
    mut v_00_u03b1_3715_: *mut crate::leanh::LeanObject,
    mut v_inst_3716_: *mut crate::leanh::LeanObject,
    mut v_x_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3718_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(v_inst_3716_, v_x_3717_);
    return v___x_3718_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith___redArg(
    mut v_inst_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ = crate::leanh::lean_alloc_closure(
        l_Lean_Lsp_instToJsonDiagnosticWith_toJson as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3720_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3720_, 1, v_inst_3719_);
    return v___x_3720_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith(
    mut v_00_u03b1_3721_: *mut crate::leanh::LeanObject,
    mut v_inst_3722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = crate::leanh::lean_alloc_closure(
        l_Lean_Lsp_instToJsonDiagnosticWith_toJson as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3723_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3723_, 1, v_inst_3722_);
    return v___x_3723_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3732_: u8 = 0;
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3732_ = 1;
    v___x_3733_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3;
    v___x_3734_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3733_, v___x_3732_);
    return v___x_3734_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5;
    v___x_3736_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4,
    );
    v___x_3737_ = lean_string_append(v___x_3736_, v___x_3735_);
    return v___x_3737_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3740_ = 1;
    v___x_3741_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6;
    v___x_3742_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3741_, v___x_3740_);
    return v___x_3742_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3743_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7,
    );
    v___x_3744_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3745_ = lean_string_append(v___x_3744_, v___x_3743_);
    return v___x_3745_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3746_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3747_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8,
    );
    v___x_3748_ = lean_string_append(v___x_3747_, v___x_3746_);
    return v___x_3748_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3752_: u8 = 0;
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3752_ = 1;
    v___x_3753_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11;
    v___x_3754_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3753_, v___x_3752_);
    return v___x_3754_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3755_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12,
    );
    v___x_3756_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3757_ = lean_string_append(v___x_3756_, v___x_3755_);
    return v___x_3757_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3758_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3759_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13,
    );
    v___x_3760_ = lean_string_append(v___x_3759_, v___x_3758_);
    return v___x_3760_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3766_: u8 = 0;
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3766_ = 1;
    v___x_3767_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17;
    v___x_3768_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3767_, v___x_3766_);
    return v___x_3768_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3769_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18,
    );
    v___x_3770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3771_ = lean_string_append(v___x_3770_, v___x_3769_);
    return v___x_3771_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3772_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3773_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19,
    );
    v___x_3774_ = lean_string_append(v___x_3773_, v___x_3772_);
    return v___x_3774_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3781_: u8 = 0;
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3781_ = 1;
    v___x_3782_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24;
    v___x_3783_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3782_, v___x_3781_);
    return v___x_3783_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3784_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25,
    );
    v___x_3785_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3786_ = lean_string_append(v___x_3785_, v___x_3784_);
    return v___x_3786_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3787_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3788_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26,
    );
    v___x_3789_ = lean_string_append(v___x_3788_, v___x_3787_);
    return v___x_3789_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3795_: u8 = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3795_ = 1;
    v___x_3796_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30;
    v___x_3797_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3796_, v___x_3795_);
    return v___x_3797_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31,
    );
    v___x_3799_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3800_ = lean_string_append(v___x_3799_, v___x_3798_);
    return v___x_3800_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3801_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3802_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32,
    );
    v___x_3803_ = lean_string_append(v___x_3802_, v___x_3801_);
    return v___x_3803_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3810_: u8 = 0;
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3810_ = 1;
    v___x_3811_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37;
    v___x_3812_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3811_, v___x_3810_);
    return v___x_3812_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3813_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38,
    );
    v___x_3814_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3815_ = lean_string_append(v___x_3814_, v___x_3813_);
    return v___x_3815_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3816_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3817_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39,
    );
    v___x_3818_ = lean_string_append(v___x_3817_, v___x_3816_);
    return v___x_3818_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3819_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13,
    );
    v___x_3820_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3821_ = lean_string_append(v___x_3820_, v___x_3819_);
    return v___x_3821_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3822_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3823_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41,
    );
    v___x_3824_ = lean_string_append(v___x_3823_, v___x_3822_);
    return v___x_3824_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3832_: u8 = 0;
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3832_ = 1;
    v___x_3833_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46;
    v___x_3834_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3833_, v___x_3832_);
    return v___x_3834_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3835_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47,
    );
    v___x_3836_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3837_ = lean_string_append(v___x_3836_, v___x_3835_);
    return v___x_3837_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3838_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48,
    );
    v___x_3840_ = lean_string_append(v___x_3839_, v___x_3838_);
    return v___x_3840_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3848_ = 1;
    v___x_3849_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53;
    v___x_3850_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3849_, v___x_3848_);
    return v___x_3850_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3851_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54,
    );
    v___x_3852_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3853_ = lean_string_append(v___x_3852_, v___x_3851_);
    return v___x_3853_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3855_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55,
    );
    v___x_3856_ = lean_string_append(v___x_3855_, v___x_3854_);
    return v___x_3856_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = 1;
    v___x_3865_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60;
    v___x_3866_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3865_, v___x_3864_);
    return v___x_3866_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61,
    );
    v___x_3868_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3869_ = lean_string_append(v___x_3868_, v___x_3867_);
    return v___x_3869_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3871_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62,
    );
    v___x_3872_ = lean_string_append(v___x_3871_, v___x_3870_);
    return v___x_3872_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3879_: u8 = 0;
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3879_ = 1;
    v___x_3880_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67;
    v___x_3881_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3880_, v___x_3879_);
    return v___x_3881_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3882_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68,
    );
    v___x_3883_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5,
    );
    v___x_3884_ = lean_string_append(v___x_3883_, v___x_3882_);
    return v___x_3884_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3886_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69,
    );
    v___x_3887_ = lean_string_append(v___x_3886_, v___x_3885_);
    return v___x_3887_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(
    mut v_inst_3888_: *mut crate::leanh::LeanObject,
    mut v_json_3889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3897_: u8 = 0;
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v_a_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3911_: u8 = 0;
    let mut v_a_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_a_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut v_a_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v_a_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3950_: u8 = 0;
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v_a_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut v_a_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut v_a_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3984_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut v_a_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3994_: u8 = 0;
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3998_: u8 = 0;
    let mut v_a_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4006_: u8 = 0;
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut v_a_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v_a_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4033_: u8 = 0;
    let mut v_a_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4037_: u8 = 0;
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4041_: u8 = 0;
    let mut v_a_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut v_a_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_a_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4071_: u8 = 0;
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_a_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut v_a_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4093_: u8 = 0;
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut v_a_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4103_: u8 = 0;
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4107_: u8 = 0;
    let mut v_a_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4115_: u8 = 0;
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4121_: u8 = 0;
    let mut v_a_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4125_: u8 = 0;
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4129_: u8 = 0;
    let mut v_a_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3890_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0;
                v___x_3891_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1;
                v___x_3892_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7;
                crate::leanh::lean_inc(v_json_3889_);
                v___x_3893_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_3890_, v___x_3892_);
                if crate::leanh::lean_obj_tag(v___x_3893_) == 0 {
                    crate::leanh::lean_dec(v_json_3889_);
                    crate::leanh::lean_dec_ref(v_inst_3888_);
                    v_a_3894_ = crate::leanh::lean_ctor_get(v___x_3893_, 0);
                    v_isSharedCheck_3903_ = (!crate::leanh::lean_is_exclusive(v___x_3893_)) as u8;
                    if v_isSharedCheck_3903_ == 0 {
                        v___x_3896_ = v___x_3893_;
                        v_isShared_3897_ = v_isSharedCheck_3903_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3894_);
                        crate::leanh::lean_dec(v___x_3893_);
                        v___x_3896_ = crate::leanh::lean_box(0);
                        v_isShared_3897_ = v_isSharedCheck_3903_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3893_) == 0 {
                        crate::leanh::lean_dec(v_json_3889_);
                        crate::leanh::lean_dec_ref(v_inst_3888_);
                        v_a_3904_ = crate::leanh::lean_ctor_get(v___x_3893_, 0);
                        v_isSharedCheck_3911_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3893_)) as u8;
                        if v_isSharedCheck_3911_ == 0 {
                            v___x_3906_ = v___x_3893_;
                            v_isShared_3907_ = v_isSharedCheck_3911_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3904_);
                            crate::leanh::lean_dec(v___x_3893_);
                            v___x_3906_ = crate::leanh::lean_box(0);
                            v_isShared_3907_ = v_isSharedCheck_3911_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3912_ = crate::leanh::lean_ctor_get(v___x_3893_, 0);
                        crate::leanh::lean_inc(v_a_3912_);
                        crate::leanh::lean_dec_ref_known(v___x_3893_, 1);
                        v___x_3913_ =
                            l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8;
                        crate::leanh::lean_inc(v_json_3889_);
                        v___x_3914_ = l_Lean_Json_getObjValAs_x3f___redArg(
                            v_json_3889_,
                            v___x_3891_,
                            v___x_3913_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3914_) == 0 {
                            crate::leanh::lean_dec(v_a_3912_);
                            crate::leanh::lean_dec(v_json_3889_);
                            crate::leanh::lean_dec_ref(v_inst_3888_);
                            v_a_3915_ = crate::leanh::lean_ctor_get(v___x_3914_, 0);
                            v_isSharedCheck_3924_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3914_)) as u8;
                            if v_isSharedCheck_3924_ == 0 {
                                v___x_3917_ = v___x_3914_;
                                v_isShared_3918_ = v_isSharedCheck_3924_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3915_);
                                crate::leanh::lean_dec(v___x_3914_);
                                v___x_3917_ = crate::leanh::lean_box(0);
                                v_isShared_3918_ = v_isSharedCheck_3924_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_3914_) == 0 {
                                crate::leanh::lean_dec(v_a_3912_);
                                crate::leanh::lean_dec(v_json_3889_);
                                crate::leanh::lean_dec_ref(v_inst_3888_);
                                v_a_3925_ = crate::leanh::lean_ctor_get(v___x_3914_, 0);
                                v_isSharedCheck_3932_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3914_)) as u8;
                                if v_isSharedCheck_3932_ == 0 {
                                    v___x_3927_ = v___x_3914_;
                                    v_isShared_3928_ = v_isSharedCheck_3932_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3925_);
                                    crate::leanh::lean_dec(v___x_3914_);
                                    v___x_3927_ = crate::leanh::lean_box(0);
                                    v_isShared_3928_ = v_isSharedCheck_3932_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3933_ = crate::leanh::lean_ctor_get(v___x_3914_, 0);
                                crate::leanh::lean_inc(v_a_3933_);
                                crate::leanh::lean_dec_ref_known(v___x_3914_, 1);
                                v___x_3934_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15;
                                v___x_3935_ =
                                    l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9;
                                crate::leanh::lean_inc(v_json_3889_);
                                v___x_3936_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                    v_json_3889_,
                                    v___x_3934_,
                                    v___x_3935_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3936_) == 0 {
                                    crate::leanh::lean_dec(v_a_3933_);
                                    crate::leanh::lean_dec(v_a_3912_);
                                    crate::leanh::lean_dec(v_json_3889_);
                                    crate::leanh::lean_dec_ref(v_inst_3888_);
                                    v_a_3937_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                                    v_isSharedCheck_3946_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3936_)) as u8;
                                    if v_isSharedCheck_3946_ == 0 {
                                        v___x_3939_ = v___x_3936_;
                                        v_isShared_3940_ = v_isSharedCheck_3946_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3937_);
                                        crate::leanh::lean_dec(v___x_3936_);
                                        v___x_3939_ = crate::leanh::lean_box(0);
                                        v_isShared_3940_ = v_isSharedCheck_3946_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_3936_) == 0 {
                                        crate::leanh::lean_dec(v_a_3933_);
                                        crate::leanh::lean_dec(v_a_3912_);
                                        crate::leanh::lean_dec(v_json_3889_);
                                        crate::leanh::lean_dec_ref(v_inst_3888_);
                                        v_a_3947_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                                        v_isSharedCheck_3954_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3936_)) as u8;
                                        if v_isSharedCheck_3954_ == 0 {
                                            v___x_3949_ = v___x_3936_;
                                            v_isShared_3950_ = v_isSharedCheck_3954_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3947_);
                                            crate::leanh::lean_dec(v___x_3936_);
                                            v___x_3949_ = crate::leanh::lean_box(0);
                                            v_isShared_3950_ = v_isSharedCheck_3954_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_3955_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                                        crate::leanh::lean_inc(v_a_3955_);
                                        crate::leanh::lean_dec_ref_known(v___x_3936_, 1);
                                        v___x_3956_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22;
                                        v___x_3957_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10;
                                        crate::leanh::lean_inc(v_json_3889_);
                                        v___x_3958_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                            v_json_3889_,
                                            v___x_3956_,
                                            v___x_3957_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_3958_) == 0 {
                                            crate::leanh::lean_dec(v_a_3955_);
                                            crate::leanh::lean_dec(v_a_3933_);
                                            crate::leanh::lean_dec(v_a_3912_);
                                            crate::leanh::lean_dec(v_json_3889_);
                                            crate::leanh::lean_dec_ref(v_inst_3888_);
                                            v_a_3959_ = crate::leanh::lean_ctor_get(v___x_3958_, 0);
                                            v_isSharedCheck_3968_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3958_))
                                                    as u8;
                                            if v_isSharedCheck_3968_ == 0 {
                                                v___x_3961_ = v___x_3958_;
                                                v_isShared_3962_ = v_isSharedCheck_3968_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3959_);
                                                crate::leanh::lean_dec(v___x_3958_);
                                                v___x_3961_ = crate::leanh::lean_box(0);
                                                v_isShared_3962_ = v_isSharedCheck_3968_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_3958_) == 0 {
                                                crate::leanh::lean_dec(v_a_3955_);
                                                crate::leanh::lean_dec(v_a_3933_);
                                                crate::leanh::lean_dec(v_a_3912_);
                                                crate::leanh::lean_dec(v_json_3889_);
                                                crate::leanh::lean_dec_ref(v_inst_3888_);
                                                v_a_3969_ =
                                                    crate::leanh::lean_ctor_get(v___x_3958_, 0);
                                                v_isSharedCheck_3976_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3958_))
                                                        as u8;
                                                if v_isSharedCheck_3976_ == 0 {
                                                    v___x_3971_ = v___x_3958_;
                                                    v_isShared_3972_ = v_isSharedCheck_3976_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3969_);
                                                    crate::leanh::lean_dec(v___x_3958_);
                                                    v___x_3971_ = crate::leanh::lean_box(0);
                                                    v_isShared_3972_ = v_isSharedCheck_3976_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_3977_ =
                                                    crate::leanh::lean_ctor_get(v___x_3958_, 0);
                                                crate::leanh::lean_inc(v_a_3977_);
                                                crate::leanh::lean_dec_ref_known(v___x_3958_, 1);
                                                v___x_3978_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28;
                                                v___x_3979_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11;
                                                crate::leanh::lean_inc(v_json_3889_);
                                                v___x_3980_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                                    v_json_3889_,
                                                    v___x_3978_,
                                                    v___x_3979_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_3980_) == 0 {
                                                    crate::leanh::lean_dec(v_a_3977_);
                                                    crate::leanh::lean_dec(v_a_3955_);
                                                    crate::leanh::lean_dec(v_a_3933_);
                                                    crate::leanh::lean_dec(v_a_3912_);
                                                    crate::leanh::lean_dec(v_json_3889_);
                                                    crate::leanh::lean_dec_ref(v_inst_3888_);
                                                    v_a_3981_ =
                                                        crate::leanh::lean_ctor_get(v___x_3980_, 0);
                                                    v_isSharedCheck_3990_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_3980_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3990_ == 0 {
                                                        v___x_3983_ = v___x_3980_;
                                                        v_isShared_3984_ = v_isSharedCheck_3990_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_3981_);
                                                        crate::leanh::lean_dec(v___x_3980_);
                                                        v___x_3983_ = crate::leanh::lean_box(0);
                                                        v_isShared_3984_ = v_isSharedCheck_3990_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if crate::leanh::lean_obj_tag(v___x_3980_) == 0
                                                    {
                                                        crate::leanh::lean_dec(v_a_3977_);
                                                        crate::leanh::lean_dec(v_a_3955_);
                                                        crate::leanh::lean_dec(v_a_3933_);
                                                        crate::leanh::lean_dec(v_a_3912_);
                                                        crate::leanh::lean_dec(v_json_3889_);
                                                        crate::leanh::lean_dec_ref(v_inst_3888_);
                                                        v_a_3991_ = crate::leanh::lean_ctor_get(
                                                            v___x_3980_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3998_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_3980_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3998_ == 0 {
                                                            v___x_3993_ = v___x_3980_;
                                                            v_isShared_3994_ =
                                                                v_isSharedCheck_3998_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_3991_);
                                                            crate::leanh::lean_dec(v___x_3980_);
                                                            v___x_3993_ = crate::leanh::lean_box(0);
                                                            v_isShared_3994_ =
                                                                v_isSharedCheck_3998_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_3999_ = crate::leanh::lean_ctor_get(
                                                            v___x_3980_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_3999_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3980_,
                                                            1,
                                                        );
                                                        v___x_4000_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35;
                                                        v___x_4001_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12;
                                                        crate::leanh::lean_inc(v_json_3889_);
                                                        v___x_4002_ =
                                                            l_Lean_Json_getObjValAs_x3f___redArg(
                                                                v_json_3889_,
                                                                v___x_4000_,
                                                                v___x_4001_,
                                                            );
                                                        if crate::leanh::lean_obj_tag(v___x_4002_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec(v_a_3999_);
                                                            crate::leanh::lean_dec(v_a_3977_);
                                                            crate::leanh::lean_dec(v_a_3955_);
                                                            crate::leanh::lean_dec(v_a_3933_);
                                                            crate::leanh::lean_dec(v_a_3912_);
                                                            crate::leanh::lean_dec(v_json_3889_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_inst_3888_,
                                                            );
                                                            v_a_4003_ = crate::leanh::lean_ctor_get(
                                                                v___x_4002_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4012_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_4002_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_4012_ == 0 {
                                                                v___x_4005_ = v___x_4002_;
                                                                v_isShared_4006_ =
                                                                    v_isSharedCheck_4012_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_4003_);
                                                                crate::leanh::lean_dec(v___x_4002_);
                                                                v___x_4005_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_4006_ =
                                                                    v_isSharedCheck_4012_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_4002_,
                                                            ) == 0
                                                            {
                                                                crate::leanh::lean_dec(v_a_3999_);
                                                                crate::leanh::lean_dec(v_a_3977_);
                                                                crate::leanh::lean_dec(v_a_3955_);
                                                                crate::leanh::lean_dec(v_a_3933_);
                                                                crate::leanh::lean_dec(v_a_3912_);
                                                                crate::leanh::lean_dec(
                                                                    v_json_3889_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_inst_3888_,
                                                                );
                                                                v_a_4013_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_4002_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_4020_ = (!crate::leanh::lean_is_exclusive(v___x_4002_)) as u8;
                                                                if v_isSharedCheck_4020_ == 0 {
                                                                    v___x_4015_ = v___x_4002_;
                                                                    v_isShared_4016_ =
                                                                        v_isSharedCheck_4020_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_4013_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_4002_,
                                                                    );
                                                                    v___x_4015_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_4016_ =
                                                                        v_isSharedCheck_4020_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_4021_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_4002_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_4021_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_4002_,
                                                                    1,
                                                                );
                                                                v___x_4022_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
                                                                crate::leanh::lean_inc(
                                                                    v_json_3889_,
                                                                );
                                                                v___x_4023_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v_inst_3888_, v___x_4022_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_4023_,
                                                                ) == 0
                                                                {
                                                                    crate::leanh::lean_dec(
                                                                        v_a_4021_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_3999_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_3977_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_3955_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_3933_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_3912_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_json_3889_,
                                                                    );
                                                                    v_a_4024_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_4023_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_4033_ = (!crate::leanh::lean_is_exclusive(v___x_4023_)) as u8;
                                                                    if v_isSharedCheck_4033_ == 0 {
                                                                        v___x_4026_ = v___x_4023_;
                                                                        v_isShared_4027_ =
                                                                            v_isSharedCheck_4033_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_4024_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_4023_,
                                                                        );
                                                                        v___x_4026_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_4027_ =
                                                                            v_isSharedCheck_4033_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_4023_,
                                                                    ) == 0
                                                                    {
                                                                        crate::leanh::lean_dec(
                                                                            v_a_4021_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_3999_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_3977_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_3955_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_3933_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_3912_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_json_3889_,
                                                                        );
                                                                        v_a_4034_ = crate::leanh::lean_ctor_get(v___x_4023_, 0);
                                                                        v_isSharedCheck_4041_ = (!crate::leanh::lean_is_exclusive(v___x_4023_)) as u8;
                                                                        if v_isSharedCheck_4041_
                                                                            == 0
                                                                        {
                                                                            v___x_4036_ =
                                                                                v___x_4023_;
                                                                            v_isShared_4037_ = v_isSharedCheck_4041_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_4034_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_4023_,
                                                                            );
                                                                            v___x_4036_ = crate::leanh::lean_box(0);
                                                                            v_isShared_4037_ = v_isSharedCheck_4041_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_4042_ = crate::leanh::lean_ctor_get(v___x_4023_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_4042_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_4023_, 1);
                                                                        v___x_4043_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44;
                                                                        v___x_4044_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13;
                                                                        crate::leanh::lean_inc(
                                                                            v_json_3889_,
                                                                        );
                                                                        v___x_4045_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_4043_, v___x_4044_);
                                                                        if crate::leanh::lean_obj_tag(v___x_4045_) == 0 {
crate::leanh::lean_dec(v_a_4042_);
crate::leanh::lean_dec(v_a_4021_);
crate::leanh::lean_dec(v_a_3999_);
crate::leanh::lean_dec(v_a_3977_);
crate::leanh::lean_dec(v_a_3955_);
crate::leanh::lean_dec(v_a_3933_);
crate::leanh::lean_dec(v_a_3912_);
crate::leanh::lean_dec(v_json_3889_);
v_a_4046_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4055_ = (!crate::leanh::lean_is_exclusive(v___x_4045_)) as u8;
if v_isSharedCheck_4055_ == 0 {
v___x_4048_ = v___x_4045_;
v_isShared_4049_ = v_isSharedCheck_4055_;
state = 29; continue;
} else {
crate::leanh::lean_inc(v_a_4046_);
crate::leanh::lean_dec(v___x_4045_);
v___x_4048_ = crate::leanh::lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4055_;
state = 29; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_4045_) == 0 {
crate::leanh::lean_dec(v_a_4042_);
crate::leanh::lean_dec(v_a_4021_);
crate::leanh::lean_dec(v_a_3999_);
crate::leanh::lean_dec(v_a_3977_);
crate::leanh::lean_dec(v_a_3955_);
crate::leanh::lean_dec(v_a_3933_);
crate::leanh::lean_dec(v_a_3912_);
crate::leanh::lean_dec(v_json_3889_);
v_a_4056_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4063_ = (!crate::leanh::lean_is_exclusive(v___x_4045_)) as u8;
if v_isSharedCheck_4063_ == 0 {
v___x_4058_ = v___x_4045_;
v_isShared_4059_ = v_isSharedCheck_4063_;
state = 31; continue;
} else {
crate::leanh::lean_inc(v_a_4056_);
crate::leanh::lean_dec(v___x_4045_);
v___x_4058_ = crate::leanh::lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
state = 31; continue;
}
} else {
v_a_4064_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
crate::leanh::lean_inc(v_a_4064_);
crate::leanh::lean_dec_ref_known(v___x_4045_, 1);
v___x_4065_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51;
v___x_4066_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14;
crate::leanh::lean_inc(v_json_3889_);
v___x_4067_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_4065_, v___x_4066_);
if crate::leanh::lean_obj_tag(v___x_4067_) == 0 {
crate::leanh::lean_dec(v_a_4064_);
crate::leanh::lean_dec(v_a_4042_);
crate::leanh::lean_dec(v_a_4021_);
crate::leanh::lean_dec(v_a_3999_);
crate::leanh::lean_dec(v_a_3977_);
crate::leanh::lean_dec(v_a_3955_);
crate::leanh::lean_dec(v_a_3933_);
crate::leanh::lean_dec(v_a_3912_);
crate::leanh::lean_dec(v_json_3889_);
v_a_4068_ = crate::leanh::lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4077_ = (!crate::leanh::lean_is_exclusive(v___x_4067_)) as u8;
if v_isSharedCheck_4077_ == 0 {
v___x_4070_ = v___x_4067_;
v_isShared_4071_ = v_isSharedCheck_4077_;
state = 33; continue;
} else {
crate::leanh::lean_inc(v_a_4068_);
crate::leanh::lean_dec(v___x_4067_);
v___x_4070_ = crate::leanh::lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4077_;
state = 33; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_4067_) == 0 {
crate::leanh::lean_dec(v_a_4064_);
crate::leanh::lean_dec(v_a_4042_);
crate::leanh::lean_dec(v_a_4021_);
crate::leanh::lean_dec(v_a_3999_);
crate::leanh::lean_dec(v_a_3977_);
crate::leanh::lean_dec(v_a_3955_);
crate::leanh::lean_dec(v_a_3933_);
crate::leanh::lean_dec(v_a_3912_);
crate::leanh::lean_dec(v_json_3889_);
v_a_4078_ = crate::leanh::lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4085_ = (!crate::leanh::lean_is_exclusive(v___x_4067_)) as u8;
if v_isSharedCheck_4085_ == 0 {
v___x_4080_ = v___x_4067_;
v_isShared_4081_ = v_isSharedCheck_4085_;
state = 35; continue;
} else {
crate::leanh::lean_inc(v_a_4078_);
crate::leanh::lean_dec(v___x_4067_);
v___x_4080_ = crate::leanh::lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
state = 35; continue;
}
} else {
v_a_4086_ = crate::leanh::lean_ctor_get(v___x_4067_, 0);
crate::leanh::lean_inc(v_a_4086_);
crate::leanh::lean_dec_ref_known(v___x_4067_, 1);
v___x_4087_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58;
v___x_4088_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15;
crate::leanh::lean_inc(v_json_3889_);
v___x_4089_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_4087_, v___x_4088_);
if crate::leanh::lean_obj_tag(v___x_4089_) == 0 {
crate::leanh::lean_dec(v_a_4086_);
crate::leanh::lean_dec(v_a_4064_);
crate::leanh::lean_dec(v_a_4042_);
crate::leanh::lean_dec(v_a_4021_);
crate::leanh::lean_dec(v_a_3999_);
crate::leanh::lean_dec(v_a_3977_);
crate::leanh::lean_dec(v_a_3955_);
crate::leanh::lean_dec(v_a_3933_);
crate::leanh::lean_dec(v_a_3912_);
crate::leanh::lean_dec(v_json_3889_);
v_a_4090_ = crate::leanh::lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4099_ = (!crate::leanh::lean_is_exclusive(v___x_4089_)) as u8;
if v_isSharedCheck_4099_ == 0 {
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4099_;
state = 37; continue;
} else {
crate::leanh::lean_inc(v_a_4090_);
crate::leanh::lean_dec(v___x_4089_);
v___x_4092_ = crate::leanh::lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4099_;
state = 37; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_4089_) == 0 {
crate::leanh::lean_dec(v_a_4086_);
crate::leanh::lean_dec(v_a_4064_);
crate::leanh::lean_dec(v_a_4042_);
crate::leanh::lean_dec(v_a_4021_);
crate::leanh::lean_dec(v_a_3999_);
crate::leanh::lean_dec(v_a_3977_);
crate::leanh::lean_dec(v_a_3955_);
crate::leanh::lean_dec(v_a_3933_);
crate::leanh::lean_dec(v_a_3912_);
crate::leanh::lean_dec(v_json_3889_);
v_a_4100_ = crate::leanh::lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4107_ = (!crate::leanh::lean_is_exclusive(v___x_4089_)) as u8;
if v_isSharedCheck_4107_ == 0 {
v___x_4102_ = v___x_4089_;
v_isShared_4103_ = v_isSharedCheck_4107_;
state = 39; continue;
} else {
crate::leanh::lean_inc(v_a_4100_);
crate::leanh::lean_dec(v___x_4089_);
v___x_4102_ = crate::leanh::lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
state = 39; continue;
}
} else {
v_a_4108_ = crate::leanh::lean_ctor_get(v___x_4089_, 0);
crate::leanh::lean_inc(v_a_4108_);
crate::leanh::lean_dec_ref_known(v___x_4089_, 1);
v___x_4109_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65;
v___x_4110_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16;
v___x_4111_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_4109_, v___x_4110_);
if crate::leanh::lean_obj_tag(v___x_4111_) == 0 {
crate::leanh::lean_dec(v_a_4108_);
crate::leanh::lean_dec(v_a_4086_);
crate::leanh::lean_dec(v_a_4064_);
crate::leanh::lean_dec(v_a_4042_);
crate::leanh::lean_dec(v_a_4021_);
crate::leanh::lean_dec(v_a_3999_);
crate::leanh::lean_dec(v_a_3977_);
crate::leanh::lean_dec(v_a_3955_);
crate::leanh::lean_dec(v_a_3933_);
crate::leanh::lean_dec(v_a_3912_);
v_a_4112_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4121_ = (!crate::leanh::lean_is_exclusive(v___x_4111_)) as u8;
if v_isSharedCheck_4121_ == 0 {
v___x_4114_ = v___x_4111_;
v_isShared_4115_ = v_isSharedCheck_4121_;
state = 41; continue;
} else {
crate::leanh::lean_inc(v_a_4112_);
crate::leanh::lean_dec(v___x_4111_);
v___x_4114_ = crate::leanh::lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4121_;
state = 41; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_4111_) == 0 {
crate::leanh::lean_dec(v_a_4108_);
crate::leanh::lean_dec(v_a_4086_);
crate::leanh::lean_dec(v_a_4064_);
crate::leanh::lean_dec(v_a_4042_);
crate::leanh::lean_dec(v_a_4021_);
crate::leanh::lean_dec(v_a_3999_);
crate::leanh::lean_dec(v_a_3977_);
crate::leanh::lean_dec(v_a_3955_);
crate::leanh::lean_dec(v_a_3933_);
crate::leanh::lean_dec(v_a_3912_);
v_a_4122_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4129_ = (!crate::leanh::lean_is_exclusive(v___x_4111_)) as u8;
if v_isSharedCheck_4129_ == 0 {
v___x_4124_ = v___x_4111_;
v_isShared_4125_ = v_isSharedCheck_4129_;
state = 43; continue;
} else {
crate::leanh::lean_inc(v_a_4122_);
crate::leanh::lean_dec(v___x_4111_);
v___x_4124_ = crate::leanh::lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
state = 43; continue;
}
} else {
v_a_4130_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4138_ = (!crate::leanh::lean_is_exclusive(v___x_4111_)) as u8;
if v_isSharedCheck_4138_ == 0 {
v___x_4132_ = v___x_4111_;
v_isShared_4133_ = v_isSharedCheck_4138_;
state = 45; continue;
} else {
crate::leanh::lean_inc(v_a_4130_);
crate::leanh::lean_dec(v___x_4111_);
v___x_4132_ = crate::leanh::lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4138_;
state = 45; continue;
}
}
}
}
}
}
}
}
}
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3898_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9,
                );
                v___x_3899_ = lean_string_append(v___x_3898_, v_a_3894_);
                crate::leanh::lean_dec(v_a_3894_);
                if v_isShared_3897_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3896_, 0, v___x_3899_);
                    v___x_3901_ = v___x_3896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3899_);
                    v___x_3901_ = v_reuseFailAlloc_3902_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3901_;
            }
            3 => {
                if v_isShared_3907_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3906_, 0);
                    v___x_3909_ = v___x_3906_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3910_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
                    v___x_3909_ = v_reuseFailAlloc_3910_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3909_;
            }
            5 => {
                v___x_3919_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14,
                );
                v___x_3920_ = lean_string_append(v___x_3919_, v_a_3915_);
                crate::leanh::lean_dec(v_a_3915_);
                if v_isShared_3918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3917_, 0, v___x_3920_);
                    v___x_3922_ = v___x_3917_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
                    v___x_3922_ = v_reuseFailAlloc_3923_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3922_;
            }
            7 => {
                if v_isShared_3928_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3927_, 0);
                    v___x_3930_ = v___x_3927_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
                    v___x_3930_ = v_reuseFailAlloc_3931_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3930_;
            }
            9 => {
                v___x_3941_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20,
                );
                v___x_3942_ = lean_string_append(v___x_3941_, v_a_3937_);
                crate::leanh::lean_dec(v_a_3937_);
                if v_isShared_3940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3939_, 0, v___x_3942_);
                    v___x_3944_ = v___x_3939_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3945_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
                    v___x_3944_ = v_reuseFailAlloc_3945_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3944_;
            }
            11 => {
                if v_isShared_3950_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3949_, 0);
                    v___x_3952_ = v___x_3949_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
                    v___x_3952_ = v_reuseFailAlloc_3953_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3952_;
            }
            13 => {
                v___x_3963_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27,
                );
                v___x_3964_ = lean_string_append(v___x_3963_, v_a_3959_);
                crate::leanh::lean_dec(v_a_3959_);
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_3964_);
                    v___x_3966_ = v___x_3961_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3964_);
                    v___x_3966_ = v_reuseFailAlloc_3967_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3966_;
            }
            15 => {
                if v_isShared_3972_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3971_, 0);
                    v___x_3974_ = v___x_3971_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
                    v___x_3974_ = v_reuseFailAlloc_3975_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3974_;
            }
            17 => {
                v___x_3985_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33,
                );
                v___x_3986_ = lean_string_append(v___x_3985_, v_a_3981_);
                crate::leanh::lean_dec(v_a_3981_);
                if v_isShared_3984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3983_, 0, v___x_3986_);
                    v___x_3988_ = v___x_3983_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3989_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3986_);
                    v___x_3988_ = v_reuseFailAlloc_3989_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3988_;
            }
            19 => {
                if v_isShared_3994_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3993_, 0);
                    v___x_3996_ = v___x_3993_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3997_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
                    v___x_3996_ = v_reuseFailAlloc_3997_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3996_;
            }
            21 => {
                v___x_4007_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40,
                );
                v___x_4008_ = lean_string_append(v___x_4007_, v_a_4003_);
                crate::leanh::lean_dec(v_a_4003_);
                if v_isShared_4006_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4005_, 0, v___x_4008_);
                    v___x_4010_ = v___x_4005_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4008_);
                    v___x_4010_ = v_reuseFailAlloc_4011_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4010_;
            }
            23 => {
                if v_isShared_4016_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4015_, 0);
                    v___x_4018_ = v___x_4015_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4018_;
            }
            25 => {
                v___x_4028_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42,
                );
                v___x_4029_ = lean_string_append(v___x_4028_, v_a_4024_);
                crate::leanh::lean_dec(v_a_4024_);
                if v_isShared_4027_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4026_, 0, v___x_4029_);
                    v___x_4031_ = v___x_4026_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4032_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4029_);
                    v___x_4031_ = v_reuseFailAlloc_4032_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4031_;
            }
            27 => {
                if v_isShared_4037_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4036_, 0);
                    v___x_4039_ = v___x_4036_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4040_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
                    v___x_4039_ = v_reuseFailAlloc_4040_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4039_;
            }
            29 => {
                v___x_4050_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49,
                );
                v___x_4051_ = lean_string_append(v___x_4050_, v_a_4046_);
                crate::leanh::lean_dec(v_a_4046_);
                if v_isShared_4049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4048_, 0, v___x_4051_);
                    v___x_4053_ = v___x_4048_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4054_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4051_);
                    v___x_4053_ = v_reuseFailAlloc_4054_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4053_;
            }
            31 => {
                if v_isShared_4059_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4058_, 0);
                    v___x_4061_ = v___x_4058_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
                    v___x_4061_ = v_reuseFailAlloc_4062_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4061_;
            }
            33 => {
                v___x_4072_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56,
                );
                v___x_4073_ = lean_string_append(v___x_4072_, v_a_4068_);
                crate::leanh::lean_dec(v_a_4068_);
                if v_isShared_4071_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4070_, 0, v___x_4073_);
                    v___x_4075_ = v___x_4070_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
                    v___x_4075_ = v_reuseFailAlloc_4076_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4075_;
            }
            35 => {
                if v_isShared_4081_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4080_, 0);
                    v___x_4083_ = v___x_4080_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
                    v___x_4083_ = v_reuseFailAlloc_4084_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4083_;
            }
            37 => {
                v___x_4094_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63,
                );
                v___x_4095_ = lean_string_append(v___x_4094_, v_a_4090_);
                crate::leanh::lean_dec(v_a_4090_);
                if v_isShared_4093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4092_, 0, v___x_4095_);
                    v___x_4097_ = v___x_4092_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4095_);
                    v___x_4097_ = v_reuseFailAlloc_4098_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4097_;
            }
            39 => {
                if v_isShared_4103_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4102_, 0);
                    v___x_4105_ = v___x_4102_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
                    v___x_4105_ = v_reuseFailAlloc_4106_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4105_;
            }
            41 => {
                v___x_4116_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70,
                );
                v___x_4117_ = lean_string_append(v___x_4116_, v_a_4112_);
                crate::leanh::lean_dec(v_a_4112_);
                if v_isShared_4115_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4114_, 0, v___x_4117_);
                    v___x_4119_ = v___x_4114_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4117_);
                    v___x_4119_ = v_reuseFailAlloc_4120_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4119_;
            }
            43 => {
                if v_isShared_4125_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4124_, 0);
                    v___x_4127_ = v___x_4124_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
                    v___x_4127_ = v_reuseFailAlloc_4128_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4127_;
            }
            45 => {
                v___x_4134_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4134_, 0, v_a_3912_);
                crate::leanh::lean_ctor_set(v___x_4134_, 1, v_a_3933_);
                crate::leanh::lean_ctor_set(v___x_4134_, 2, v_a_3955_);
                crate::leanh::lean_ctor_set(v___x_4134_, 3, v_a_3977_);
                crate::leanh::lean_ctor_set(v___x_4134_, 4, v_a_3999_);
                crate::leanh::lean_ctor_set(v___x_4134_, 5, v_a_4021_);
                crate::leanh::lean_ctor_set(v___x_4134_, 6, v_a_4042_);
                crate::leanh::lean_ctor_set(v___x_4134_, 7, v_a_4064_);
                crate::leanh::lean_ctor_set(v___x_4134_, 8, v_a_4086_);
                crate::leanh::lean_ctor_set(v___x_4134_, 9, v_a_4108_);
                crate::leanh::lean_ctor_set(v___x_4134_, 10, v_a_4130_);
                if v_isShared_4133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4132_, 0, v___x_4134_);
                    v___x_4136_ = v___x_4132_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
                    v___x_4136_ = v_reuseFailAlloc_4137_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_4136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson(
    mut v_00_u03b1_4139_: *mut crate::leanh::LeanObject,
    mut v_inst_4140_: *mut crate::leanh::LeanObject,
    mut v_json_4141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ =
        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(v_inst_4140_, v_json_4141_);
    return v___x_4142_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(
    mut v_inst_4143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4144_ = crate::leanh::lean_alloc_closure(
        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4144_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4144_, 1, v_inst_4143_);
    return v___x_4144_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticWith(
    mut v_00_u03b1_4145_: *mut crate::leanh::LeanObject,
    mut v_inst_4146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4147_ = crate::leanh::lean_alloc_closure(
        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4147_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4147_, 1, v_inst_4146_);
    return v___x_4147_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticWith_fullRange___redArg(
    mut v_d_4148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fullRange_x3f_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fullRange_x3f_4149_ = crate::leanh::lean_ctor_get(v_d_4148_, 1);
    if crate::leanh::lean_obj_tag(v_fullRange_x3f_4149_) == 0 {
        let mut v_range_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_range_4150_ = crate::leanh::lean_ctor_get(v_d_4148_, 0);
        crate::leanh::lean_inc_ref(v_range_4150_);
        return v_range_4150_;
    } else {
        let mut v_val_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4151_ = crate::leanh::lean_ctor_get(v_fullRange_x3f_4149_, 0);
        crate::leanh::lean_inc(v_val_4151_);
        return v_val_4151_;
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(
    mut v_d_4152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4153_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_4152_);
    crate::leanh::lean_dec_ref(v_d_4152_);
    return v_res_4153_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticWith_fullRange(
    mut v_00_u03b1_4154_: *mut crate::leanh::LeanObject,
    mut v_d_4155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_4155_);
    return v___x_4156_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticWith_fullRange___boxed(
    mut v_00_u03b1_4157_: *mut crate::leanh::LeanObject,
    mut v_d_4158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_Lean_Lsp_DiagnosticWith_fullRange(v_00_u03b1_4157_, v_d_4158_);
    crate::leanh::lean_dec_ref(v_d_4158_);
    return v_res_4159_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(
    mut v_x_4168_: *mut crate::leanh::LeanObject,
    mut v_x_4169_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4168_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4169_) == 0 {
            let mut v___x_4170_: u8 = 0;
            v___x_4170_ = 1;
            return v___x_4170_;
        } else {
            let mut v___x_4171_: u8 = 0;
            v___x_4171_ = 0;
            return v___x_4171_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4169_) == 0 {
            let mut v___x_4172_: u8 = 0;
            v___x_4172_ = 0;
            return v___x_4172_;
        } else {
            let mut v_val_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4175_: u8 = 0;
            v_val_4173_ = crate::leanh::lean_ctor_get(v_x_4168_, 0);
            v_val_4174_ = crate::leanh::lean_ctor_get(v_x_4169_, 0);
            v___x_4175_ = lean_int_dec_eq(v_val_4173_, v_val_4174_);
            return v___x_4175_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(
    mut v_x_4176_: *mut crate::leanh::LeanObject,
    mut v_x_4177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4178_: u8 = 0;
    let mut v_r_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4178_ =
        l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(
            v_x_4176_, v_x_4177_,
        );
    crate::leanh::lean_dec(v_x_4177_);
    crate::leanh::lean_dec(v_x_4176_);
    v_r_4179_ = crate::leanh::lean_box((v_res_4178_) as usize);
    return v_r_4179_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(
    mut v_x_4180_: *mut crate::leanh::LeanObject,
    mut v_x_4181_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4180_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4181_) == 0 {
            let mut v___x_4182_: u8 = 0;
            v___x_4182_ = 1;
            return v___x_4182_;
        } else {
            let mut v___x_4183_: u8 = 0;
            v___x_4183_ = 0;
            return v___x_4183_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4181_) == 0 {
            let mut v___x_4184_: u8 = 0;
            v___x_4184_ = 0;
            return v___x_4184_;
        } else {
            let mut v_val_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4186_: u8 = 0;
            v_val_4185_ = crate::leanh::lean_ctor_get(v_x_4180_, 0);
            v___x_4186_ = (crate::leanh::lean_unbox(v_val_4185_) as u8);
            if v___x_4186_ == 0 {
                let mut v_val_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4188_: u8 = 0;
                v_val_4187_ = crate::leanh::lean_ctor_get(v_x_4181_, 0);
                v___x_4188_ = (crate::leanh::lean_unbox(v_val_4187_) as u8);
                if v___x_4188_ == 0 {
                    let mut v___x_4189_: u8 = 0;
                    v___x_4189_ = 1;
                    return v___x_4189_;
                } else {
                    let mut v___x_4190_: u8 = 0;
                    v___x_4190_ = (crate::leanh::lean_unbox(v_val_4185_) as u8);
                    return v___x_4190_;
                }
            } else {
                let mut v_val_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4192_: u8 = 0;
                v_val_4191_ = crate::leanh::lean_ctor_get(v_x_4181_, 0);
                v___x_4192_ = (crate::leanh::lean_unbox(v_val_4191_) as u8);
                return v___x_4192_;
            }
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(
    mut v_x_4193_: *mut crate::leanh::LeanObject,
    mut v_x_4194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4195_: u8 = 0;
    let mut v_r_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4195_ =
        l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(
            v_x_4193_, v_x_4194_,
        );
    crate::leanh::lean_dec(v_x_4194_);
    crate::leanh::lean_dec(v_x_4193_);
    v_r_4196_ = crate::leanh::lean_box((v_res_4195_) as usize);
    return v_r_4196_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(
    mut v_xs_4197_: *mut crate::leanh::LeanObject,
    mut v_ys_4198_: *mut crate::leanh::LeanObject,
    mut v_x_4199_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4201_: u8 = 0;
    let mut v_one_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4200_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4201_ = lean_nat_dec_eq(v_x_4199_, v_zero_4200_);
                if v_isZero_4201_ == 1 {
                    crate::leanh::lean_dec(v_x_4199_);
                    return v_isZero_4201_;
                } else {
                    v_one_4202_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4203_ = lean_nat_sub(v_x_4199_, v_one_4202_);
                    crate::leanh::lean_dec(v_x_4199_);
                    v___x_4204_ = lean_array_fget_borrowed(v_xs_4197_, v_n_4203_);
                    v___x_4205_ = lean_array_fget_borrowed(v_ys_4198_, v_n_4203_);
                    v___x_4206_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(
                        v___x_4204_,
                        v___x_4205_,
                    );
                    if v___x_4206_ == 0 {
                        crate::leanh::lean_dec(v_n_4203_);
                        return v___x_4206_;
                    } else {
                        v_x_4199_ = v_n_4203_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg___boxed(
    mut v_xs_4208_: *mut crate::leanh::LeanObject,
    mut v_ys_4209_: *mut crate::leanh::LeanObject,
    mut v_x_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4211_: u8 = 0;
    let mut v_r_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_4208_, v_ys_4209_, v_x_4210_);
    crate::leanh::lean_dec_ref(v_ys_4209_);
    crate::leanh::lean_dec_ref(v_xs_4208_);
    v_r_4212_ = crate::leanh::lean_box((v_res_4211_) as usize);
    return v_r_4212_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(
    mut v_x_4213_: *mut crate::leanh::LeanObject,
    mut v_x_4214_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4213_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4214_) == 0 {
            let mut v___x_4215_: u8 = 0;
            v___x_4215_ = 1;
            return v___x_4215_;
        } else {
            let mut v___x_4216_: u8 = 0;
            v___x_4216_ = 0;
            return v___x_4216_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4214_) == 0 {
            let mut v___x_4217_: u8 = 0;
            v___x_4217_ = 0;
            return v___x_4217_;
        } else {
            let mut v_val_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4222_: u8 = 0;
            v_val_4218_ = crate::leanh::lean_ctor_get(v_x_4213_, 0);
            v_val_4219_ = crate::leanh::lean_ctor_get(v_x_4214_, 0);
            v___x_4220_ = lean_array_get_size(v_val_4218_);
            v___x_4221_ = lean_array_get_size(v_val_4219_);
            v___x_4222_ = lean_nat_dec_eq(v___x_4220_, v___x_4221_);
            if v___x_4222_ == 0 {
                return v___x_4222_;
            } else {
                let mut v___x_4223_: u8 = 0;
                v___x_4223_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_val_4218_, v_val_4219_, v___x_4220_);
                return v___x_4223_;
            }
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8___boxed(
    mut v_x_4224_: *mut crate::leanh::LeanObject,
    mut v_x_4225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4226_: u8 = 0;
    let mut v_r_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4226_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_x_4224_, v_x_4225_);
    crate::leanh::lean_dec(v_x_4225_);
    crate::leanh::lean_dec(v_x_4224_);
    v_r_4227_ = crate::leanh::lean_box((v_res_4226_) as usize);
    return v_r_4227_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(
    mut v_xs_4228_: *mut crate::leanh::LeanObject,
    mut v_ys_4229_: *mut crate::leanh::LeanObject,
    mut v_x_4230_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4232_: u8 = 0;
    let mut v_one_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: u8 = 0;
    let mut v___x_4238_: u8 = 0;
    let mut v___x_4239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4231_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4232_ = lean_nat_dec_eq(v_x_4230_, v_zero_4231_);
                if v_isZero_4232_ == 1 {
                    crate::leanh::lean_dec(v_x_4230_);
                    return v_isZero_4232_;
                } else {
                    v_one_4233_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4234_ = lean_nat_sub(v_x_4230_, v_one_4233_);
                    crate::leanh::lean_dec(v_x_4230_);
                    v___x_4235_ = lean_array_fget_borrowed(v_xs_4228_, v_n_4234_);
                    v___x_4236_ = lean_array_fget_borrowed(v_ys_4229_, v_n_4234_);
                    v___x_4237_ = (crate::leanh::lean_unbox(v___x_4235_) as u8);
                    v___x_4238_ = (crate::leanh::lean_unbox(v___x_4236_) as u8);
                    v___x_4239_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v___x_4237_, v___x_4238_);
                    if v___x_4239_ == 0 {
                        crate::leanh::lean_dec(v_n_4234_);
                        return v___x_4239_;
                    } else {
                        v_x_4230_ = v_n_4234_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg___boxed(
    mut v_xs_4241_: *mut crate::leanh::LeanObject,
    mut v_ys_4242_: *mut crate::leanh::LeanObject,
    mut v_x_4243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4244_: u8 = 0;
    let mut v_r_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4244_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_4241_, v_ys_4242_, v_x_4243_);
    crate::leanh::lean_dec_ref(v_ys_4242_);
    crate::leanh::lean_dec_ref(v_xs_4241_);
    v_r_4245_ = crate::leanh::lean_box((v_res_4244_) as usize);
    return v_r_4245_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(
    mut v_x_4246_: *mut crate::leanh::LeanObject,
    mut v_x_4247_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4246_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4247_) == 0 {
            let mut v___x_4248_: u8 = 0;
            v___x_4248_ = 1;
            return v___x_4248_;
        } else {
            let mut v___x_4249_: u8 = 0;
            v___x_4249_ = 0;
            return v___x_4249_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4247_) == 0 {
            let mut v___x_4250_: u8 = 0;
            v___x_4250_ = 0;
            return v___x_4250_;
        } else {
            let mut v_val_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4255_: u8 = 0;
            v_val_4251_ = crate::leanh::lean_ctor_get(v_x_4246_, 0);
            v_val_4252_ = crate::leanh::lean_ctor_get(v_x_4247_, 0);
            v___x_4253_ = lean_array_get_size(v_val_4251_);
            v___x_4254_ = lean_array_get_size(v_val_4252_);
            v___x_4255_ = lean_nat_dec_eq(v___x_4253_, v___x_4254_);
            if v___x_4255_ == 0 {
                return v___x_4255_;
            } else {
                let mut v___x_4256_: u8 = 0;
                v___x_4256_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_val_4251_, v_val_4252_, v___x_4253_);
                return v___x_4256_;
            }
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7___boxed(
    mut v_x_4257_: *mut crate::leanh::LeanObject,
    mut v_x_4258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4259_: u8 = 0;
    let mut v_r_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_x_4257_, v_x_4258_);
    crate::leanh::lean_dec(v_x_4258_);
    crate::leanh::lean_dec(v_x_4257_);
    v_r_4260_ = crate::leanh::lean_box((v_res_4259_) as usize);
    return v_r_4260_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(
    mut v_x_4261_: *mut crate::leanh::LeanObject,
    mut v_x_4262_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4261_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4262_) == 0 {
            let mut v___x_4263_: u8 = 0;
            v___x_4263_ = 1;
            return v___x_4263_;
        } else {
            let mut v___x_4264_: u8 = 0;
            v___x_4264_ = 0;
            return v___x_4264_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4262_) == 0 {
            let mut v___x_4265_: u8 = 0;
            v___x_4265_ = 0;
            return v___x_4265_;
        } else {
            let mut v_val_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4268_: u8 = 0;
            v_val_4266_ = crate::leanh::lean_ctor_get(v_x_4261_, 0);
            v_val_4267_ = crate::leanh::lean_ctor_get(v_x_4262_, 0);
            v___x_4268_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_val_4266_, v_val_4267_);
            return v___x_4268_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4___boxed(
    mut v_x_4269_: *mut crate::leanh::LeanObject,
    mut v_x_4270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4271_: u8 = 0;
    let mut v_r_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4271_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_x_4269_, v_x_4270_);
    crate::leanh::lean_dec(v_x_4270_);
    crate::leanh::lean_dec(v_x_4269_);
    v_r_4272_ = crate::leanh::lean_box((v_res_4271_) as usize);
    return v_r_4272_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(
    mut v_x_4273_: *mut crate::leanh::LeanObject,
    mut v_x_4274_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4273_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4274_) == 0 {
            let mut v___x_4275_: u8 = 0;
            v___x_4275_ = 1;
            return v___x_4275_;
        } else {
            let mut v___x_4276_: u8 = 0;
            v___x_4276_ = 0;
            return v___x_4276_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4274_) == 0 {
            let mut v___x_4277_: u8 = 0;
            v___x_4277_ = 0;
            return v___x_4277_;
        } else {
            let mut v_val_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4280_: u8 = 0;
            v_val_4278_ = crate::leanh::lean_ctor_get(v_x_4273_, 0);
            v_val_4279_ = crate::leanh::lean_ctor_get(v_x_4274_, 0);
            v___x_4280_ = l_Lean_Lsp_instBEqRange_beq(v_val_4278_, v_val_4279_);
            return v___x_4280_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2___boxed(
    mut v_x_4281_: *mut crate::leanh::LeanObject,
    mut v_x_4282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4283_: u8 = 0;
    let mut v_r_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4283_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_x_4281_, v_x_4282_);
    crate::leanh::lean_dec(v_x_4282_);
    crate::leanh::lean_dec(v_x_4281_);
    v_r_4284_ = crate::leanh::lean_box((v_res_4283_) as usize);
    return v_r_4284_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(
    mut v_x_4285_: *mut crate::leanh::LeanObject,
    mut v_x_4286_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4285_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4286_) == 0 {
            let mut v___x_4287_: u8 = 0;
            v___x_4287_ = 1;
            return v___x_4287_;
        } else {
            let mut v___x_4288_: u8 = 0;
            v___x_4288_ = 0;
            return v___x_4288_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4286_) == 0 {
            let mut v___x_4289_: u8 = 0;
            v___x_4289_ = 0;
            return v___x_4289_;
        } else {
            let mut v_val_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4292_: u8 = 0;
            v_val_4290_ = crate::leanh::lean_ctor_get(v_x_4285_, 0);
            v_val_4291_ = crate::leanh::lean_ctor_get(v_x_4286_, 0);
            v___x_4292_ =
                l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_val_4290_, v_val_4291_);
            return v___x_4292_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9___boxed(
    mut v_x_4293_: *mut crate::leanh::LeanObject,
    mut v_x_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4295_: u8 = 0;
    let mut v_r_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4295_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_x_4293_, v_x_4294_);
    crate::leanh::lean_dec(v_x_4294_);
    crate::leanh::lean_dec(v_x_4293_);
    v_r_4296_ = crate::leanh::lean_box((v_res_4295_) as usize);
    return v_r_4296_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(
    mut v_x_4297_: *mut crate::leanh::LeanObject,
    mut v_x_4298_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4297_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4298_) == 0 {
            let mut v___x_4299_: u8 = 0;
            v___x_4299_ = 1;
            return v___x_4299_;
        } else {
            let mut v___x_4300_: u8 = 0;
            v___x_4300_ = 0;
            return v___x_4300_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4298_) == 0 {
            let mut v___x_4301_: u8 = 0;
            v___x_4301_ = 0;
            return v___x_4301_;
        } else {
            let mut v_val_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4304_: u8 = 0;
            v_val_4302_ = crate::leanh::lean_ctor_get(v_x_4297_, 0);
            v_val_4303_ = crate::leanh::lean_ctor_get(v_x_4298_, 0);
            v___x_4304_ = lean_string_dec_eq(v_val_4302_, v_val_4303_);
            return v___x_4304_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5___boxed(
    mut v_x_4305_: *mut crate::leanh::LeanObject,
    mut v_x_4306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4307_: u8 = 0;
    let mut v_r_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4307_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_x_4305_, v_x_4306_);
    crate::leanh::lean_dec(v_x_4306_);
    crate::leanh::lean_dec(v_x_4305_);
    v_r_4308_ = crate::leanh::lean_box((v_res_4307_) as usize);
    return v_r_4308_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(
    mut v_xs_4309_: *mut crate::leanh::LeanObject,
    mut v_ys_4310_: *mut crate::leanh::LeanObject,
    mut v_x_4311_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4313_: u8 = 0;
    let mut v_one_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: u8 = 0;
    let mut v___x_4319_: u8 = 0;
    let mut v___x_4320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4312_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4313_ = lean_nat_dec_eq(v_x_4311_, v_zero_4312_);
                if v_isZero_4313_ == 1 {
                    crate::leanh::lean_dec(v_x_4311_);
                    return v_isZero_4313_;
                } else {
                    v_one_4314_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4315_ = lean_nat_sub(v_x_4311_, v_one_4314_);
                    crate::leanh::lean_dec(v_x_4311_);
                    v___x_4316_ = lean_array_fget_borrowed(v_xs_4309_, v_n_4315_);
                    v___x_4317_ = lean_array_fget_borrowed(v_ys_4310_, v_n_4315_);
                    v___x_4318_ = (crate::leanh::lean_unbox(v___x_4316_) as u8);
                    v___x_4319_ = (crate::leanh::lean_unbox(v___x_4317_) as u8);
                    v___x_4320_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v___x_4318_, v___x_4319_);
                    if v___x_4320_ == 0 {
                        crate::leanh::lean_dec(v_n_4315_);
                        return v___x_4320_;
                    } else {
                        v_x_4311_ = v_n_4315_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg___boxed(
    mut v_xs_4322_: *mut crate::leanh::LeanObject,
    mut v_ys_4323_: *mut crate::leanh::LeanObject,
    mut v_x_4324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4325_: u8 = 0;
    let mut v_r_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4325_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_4322_, v_ys_4323_, v_x_4324_);
    crate::leanh::lean_dec_ref(v_ys_4323_);
    crate::leanh::lean_dec_ref(v_xs_4322_);
    v_r_4326_ = crate::leanh::lean_box((v_res_4325_) as usize);
    return v_r_4326_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(
    mut v_x_4327_: *mut crate::leanh::LeanObject,
    mut v_x_4328_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4327_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4328_) == 0 {
            let mut v___x_4329_: u8 = 0;
            v___x_4329_ = 1;
            return v___x_4329_;
        } else {
            let mut v___x_4330_: u8 = 0;
            v___x_4330_ = 0;
            return v___x_4330_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4328_) == 0 {
            let mut v___x_4331_: u8 = 0;
            v___x_4331_ = 0;
            return v___x_4331_;
        } else {
            let mut v_val_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4336_: u8 = 0;
            v_val_4332_ = crate::leanh::lean_ctor_get(v_x_4327_, 0);
            v_val_4333_ = crate::leanh::lean_ctor_get(v_x_4328_, 0);
            v___x_4334_ = lean_array_get_size(v_val_4332_);
            v___x_4335_ = lean_array_get_size(v_val_4333_);
            v___x_4336_ = lean_nat_dec_eq(v___x_4334_, v___x_4335_);
            if v___x_4336_ == 0 {
                return v___x_4336_;
            } else {
                let mut v___x_4337_: u8 = 0;
                v___x_4337_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_val_4332_, v_val_4333_, v___x_4334_);
                return v___x_4337_;
            }
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6___boxed(
    mut v_x_4338_: *mut crate::leanh::LeanObject,
    mut v_x_4339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4340_: u8 = 0;
    let mut v_r_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_x_4338_, v_x_4339_);
    crate::leanh::lean_dec(v_x_4339_);
    crate::leanh::lean_dec(v_x_4338_);
    v_r_4341_ = crate::leanh::lean_box((v_res_4340_) as usize);
    return v_r_4341_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(
    mut v_x_4342_: *mut crate::leanh::LeanObject,
    mut v_x_4343_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4342_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4343_) == 0 {
            let mut v___x_4344_: u8 = 0;
            v___x_4344_ = 1;
            return v___x_4344_;
        } else {
            let mut v___x_4345_: u8 = 0;
            v___x_4345_ = 0;
            return v___x_4345_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4343_) == 0 {
            let mut v___x_4346_: u8 = 0;
            v___x_4346_ = 0;
            return v___x_4346_;
        } else {
            let mut v_val_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4349_: u8 = 0;
            let mut v___x_4350_: u8 = 0;
            let mut v___x_4351_: u8 = 0;
            v_val_4347_ = crate::leanh::lean_ctor_get(v_x_4342_, 0);
            v_val_4348_ = crate::leanh::lean_ctor_get(v_x_4343_, 0);
            v___x_4349_ = (crate::leanh::lean_unbox(v_val_4347_) as u8);
            v___x_4350_ = (crate::leanh::lean_unbox(v_val_4348_) as u8);
            v___x_4351_ = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v___x_4349_, v___x_4350_);
            return v___x_4351_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3___boxed(
    mut v_x_4352_: *mut crate::leanh::LeanObject,
    mut v_x_4353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4354_: u8 = 0;
    let mut v_r_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4354_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_x_4352_, v_x_4353_);
    crate::leanh::lean_dec(v_x_4353_);
    crate::leanh::lean_dec(v_x_4352_);
    v_r_4355_ = crate::leanh::lean_box((v_res_4354_) as usize);
    return v_r_4355_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(
    mut v_x_4356_: *mut crate::leanh::LeanObject,
    mut v_x_4357_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_range_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    v_range_4358_ = crate::leanh::lean_ctor_get(v_x_4356_, 0);
    v_fullRange_x3f_4359_ = crate::leanh::lean_ctor_get(v_x_4356_, 1);
    v_severity_x3f_4360_ = crate::leanh::lean_ctor_get(v_x_4356_, 2);
    v_isSilent_x3f_4361_ = crate::leanh::lean_ctor_get(v_x_4356_, 3);
    v_code_x3f_4362_ = crate::leanh::lean_ctor_get(v_x_4356_, 4);
    v_source_x3f_4363_ = crate::leanh::lean_ctor_get(v_x_4356_, 5);
    v_message_4364_ = crate::leanh::lean_ctor_get(v_x_4356_, 6);
    v_tags_x3f_4365_ = crate::leanh::lean_ctor_get(v_x_4356_, 7);
    v_leanTags_x3f_4366_ = crate::leanh::lean_ctor_get(v_x_4356_, 8);
    v_relatedInformation_x3f_4367_ = crate::leanh::lean_ctor_get(v_x_4356_, 9);
    v_data_x3f_4368_ = crate::leanh::lean_ctor_get(v_x_4356_, 10);
    v_range_4369_ = crate::leanh::lean_ctor_get(v_x_4357_, 0);
    v_fullRange_x3f_4370_ = crate::leanh::lean_ctor_get(v_x_4357_, 1);
    v_severity_x3f_4371_ = crate::leanh::lean_ctor_get(v_x_4357_, 2);
    v_isSilent_x3f_4372_ = crate::leanh::lean_ctor_get(v_x_4357_, 3);
    v_code_x3f_4373_ = crate::leanh::lean_ctor_get(v_x_4357_, 4);
    v_source_x3f_4374_ = crate::leanh::lean_ctor_get(v_x_4357_, 5);
    v_message_4375_ = crate::leanh::lean_ctor_get(v_x_4357_, 6);
    v_tags_x3f_4376_ = crate::leanh::lean_ctor_get(v_x_4357_, 7);
    v_leanTags_x3f_4377_ = crate::leanh::lean_ctor_get(v_x_4357_, 8);
    v_relatedInformation_x3f_4378_ = crate::leanh::lean_ctor_get(v_x_4357_, 9);
    v_data_x3f_4379_ = crate::leanh::lean_ctor_get(v_x_4357_, 10);
    v___x_4380_ = l_Lean_Lsp_instBEqRange_beq(v_range_4358_, v_range_4369_);
    if v___x_4380_ == 0 {
        return v___x_4380_;
    } else {
        let mut v___x_4381_: u8 = 0;
        v___x_4381_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_fullRange_x3f_4359_, v_fullRange_x3f_4370_);
        if v___x_4381_ == 0 {
            return v___x_4381_;
        } else {
            let mut v___x_4382_: u8 = 0;
            v___x_4382_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_severity_x3f_4360_, v_severity_x3f_4371_);
            if v___x_4382_ == 0 {
                return v___x_4382_;
            } else {
                let mut v___x_4383_: u8 = 0;
                v___x_4383_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v_isSilent_x3f_4361_, v_isSilent_x3f_4372_);
                if v___x_4383_ == 0 {
                    return v___x_4383_;
                } else {
                    let mut v___x_4384_: u8 = 0;
                    v___x_4384_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_code_x3f_4362_, v_code_x3f_4373_);
                    if v___x_4384_ == 0 {
                        return v___x_4384_;
                    } else {
                        let mut v___x_4385_: u8 = 0;
                        v___x_4385_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_source_x3f_4363_, v_source_x3f_4374_);
                        if v___x_4385_ == 0 {
                            return v___x_4385_;
                        } else {
                            let mut v___x_4386_: u8 = 0;
                            v___x_4386_ = lean_string_dec_eq(v_message_4364_, v_message_4375_);
                            if v___x_4386_ == 0 {
                                return v___x_4386_;
                            } else {
                                let mut v___x_4387_: u8 = 0;
                                v___x_4387_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_tags_x3f_4365_, v_tags_x3f_4376_);
                                if v___x_4387_ == 0 {
                                    return v___x_4387_;
                                } else {
                                    let mut v___x_4388_: u8 = 0;
                                    v___x_4388_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_leanTags_x3f_4366_, v_leanTags_x3f_4377_);
                                    if v___x_4388_ == 0 {
                                        return v___x_4388_;
                                    } else {
                                        let mut v___x_4389_: u8 = 0;
                                        v___x_4389_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_relatedInformation_x3f_4367_, v_relatedInformation_x3f_4378_);
                                        if v___x_4389_ == 0 {
                                            return v___x_4389_;
                                        } else {
                                            let mut v___x_4390_: u8 = 0;
                                            v___x_4390_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_data_x3f_4368_, v_data_x3f_4379_);
                                            return v___x_4390_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___boxed(
    mut v_x_4391_: *mut crate::leanh::LeanObject,
    mut v_x_4392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4393_: u8 = 0;
    let mut v_r_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4393_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v_x_4391_, v_x_4392_);
    crate::leanh::lean_dec_ref(v_x_4392_);
    crate::leanh::lean_dec_ref(v_x_4391_);
    v_r_4394_ = crate::leanh::lean_box((v_res_4393_) as usize);
    return v_r_4394_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(
    mut v_xs_4395_: *mut crate::leanh::LeanObject,
    mut v_ys_4396_: *mut crate::leanh::LeanObject,
    mut v_x_4397_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4399_: u8 = 0;
    let mut v_one_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4398_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4399_ = lean_nat_dec_eq(v_x_4397_, v_zero_4398_);
                if v_isZero_4399_ == 1 {
                    crate::leanh::lean_dec(v_x_4397_);
                    return v_isZero_4399_;
                } else {
                    v_one_4400_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4401_ = lean_nat_sub(v_x_4397_, v_one_4400_);
                    crate::leanh::lean_dec(v_x_4397_);
                    v___x_4402_ = lean_array_fget_borrowed(v_xs_4395_, v_n_4401_);
                    v___x_4403_ = lean_array_fget_borrowed(v_ys_4396_, v_n_4401_);
                    v___x_4404_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v___x_4402_, v___x_4403_);
                    if v___x_4404_ == 0 {
                        crate::leanh::lean_dec(v_n_4401_);
                        return v___x_4404_;
                    } else {
                        v_x_4397_ = v_n_4401_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg___boxed(
    mut v_xs_4406_: *mut crate::leanh::LeanObject,
    mut v_ys_4407_: *mut crate::leanh::LeanObject,
    mut v_x_4408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4409_: u8 = 0;
    let mut v_r_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4409_ =
        l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(
            v_xs_4406_, v_ys_4407_, v_x_4408_,
        );
    crate::leanh::lean_dec_ref(v_ys_4407_);
    crate::leanh::lean_dec_ref(v_xs_4406_);
    v_r_4410_ = crate::leanh::lean_box((v_res_4409_) as usize);
    return v_r_4410_;
}
pub unsafe fn l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(
    mut v_x_4411_: *mut crate::leanh::LeanObject,
    mut v_x_4412_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_uri_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isIncremental_x3f_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isIncremental_x3f_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    v_uri_4413_ = crate::leanh::lean_ctor_get(v_x_4411_, 0);
    v_version_x3f_4414_ = crate::leanh::lean_ctor_get(v_x_4411_, 1);
    v_isIncremental_x3f_4415_ = crate::leanh::lean_ctor_get(v_x_4411_, 2);
    v_diagnostics_4416_ = crate::leanh::lean_ctor_get(v_x_4411_, 3);
    v_uri_4417_ = crate::leanh::lean_ctor_get(v_x_4412_, 0);
    v_version_x3f_4418_ = crate::leanh::lean_ctor_get(v_x_4412_, 1);
    v_isIncremental_x3f_4419_ = crate::leanh::lean_ctor_get(v_x_4412_, 2);
    v_diagnostics_4420_ = crate::leanh::lean_ctor_get(v_x_4412_, 3);
    v___x_4421_ = lean_string_dec_eq(v_uri_4413_, v_uri_4417_);
    if v___x_4421_ == 0 {
        return v___x_4421_;
    } else {
        let mut v___x_4422_: u8 = 0;
        v___x_4422_ =
            l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(
                v_version_x3f_4414_,
                v_version_x3f_4418_,
            );
        if v___x_4422_ == 0 {
            return v___x_4422_;
        } else {
            let mut v___x_4423_: u8 = 0;
            v___x_4423_ =
                l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(
                    v_isIncremental_x3f_4415_,
                    v_isIncremental_x3f_4419_,
                );
            if v___x_4423_ == 0 {
                return v___x_4423_;
            } else {
                let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4426_: u8 = 0;
                v___x_4424_ = lean_array_get_size(v_diagnostics_4416_);
                v___x_4425_ = lean_array_get_size(v_diagnostics_4420_);
                v___x_4426_ = lean_nat_dec_eq(v___x_4424_, v___x_4425_);
                if v___x_4426_ == 0 {
                    return v___x_4426_;
                } else {
                    let mut v___x_4427_: u8 = 0;
                    v___x_4427_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_diagnostics_4416_, v_diagnostics_4420_, v___x_4424_);
                    return v___x_4427_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed(
    mut v_x_4428_: *mut crate::leanh::LeanObject,
    mut v_x_4429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4430_: u8 = 0;
    let mut v_r_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4430_ = l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(v_x_4428_, v_x_4429_);
    crate::leanh::lean_dec_ref(v_x_4429_);
    crate::leanh::lean_dec_ref(v_x_4428_);
    v_r_4431_ = crate::leanh::lean_box((v_res_4430_) as usize);
    return v_r_4431_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(
    mut v_xs_4432_: *mut crate::leanh::LeanObject,
    mut v_ys_4433_: *mut crate::leanh::LeanObject,
    mut v_hsz_4434_: *mut crate::leanh::LeanObject,
    mut v_x_4435_: *mut crate::leanh::LeanObject,
    mut v_x_4436_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4437_: u8 = 0;
    v___x_4437_ =
        l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(
            v_xs_4432_, v_ys_4433_, v_x_4435_,
        );
    return v___x_4437_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___boxed(
    mut v_xs_4438_: *mut crate::leanh::LeanObject,
    mut v_ys_4439_: *mut crate::leanh::LeanObject,
    mut v_hsz_4440_: *mut crate::leanh::LeanObject,
    mut v_x_4441_: *mut crate::leanh::LeanObject,
    mut v_x_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4443_: u8 = 0;
    let mut v_r_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4443_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(
        v_xs_4438_,
        v_ys_4439_,
        v_hsz_4440_,
        v_x_4441_,
        v_x_4442_,
    );
    crate::leanh::lean_dec_ref(v_ys_4439_);
    crate::leanh::lean_dec_ref(v_xs_4438_);
    v_r_4444_ = crate::leanh::lean_box((v_res_4443_) as usize);
    return v_r_4444_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(
    mut v_xs_4445_: *mut crate::leanh::LeanObject,
    mut v_ys_4446_: *mut crate::leanh::LeanObject,
    mut v_hsz_4447_: *mut crate::leanh::LeanObject,
    mut v_x_4448_: *mut crate::leanh::LeanObject,
    mut v_x_4449_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4450_: u8 = 0;
    v___x_4450_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_4445_, v_ys_4446_, v_x_4448_);
    return v___x_4450_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___boxed(
    mut v_xs_4451_: *mut crate::leanh::LeanObject,
    mut v_ys_4452_: *mut crate::leanh::LeanObject,
    mut v_hsz_4453_: *mut crate::leanh::LeanObject,
    mut v_x_4454_: *mut crate::leanh::LeanObject,
    mut v_x_4455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4456_: u8 = 0;
    let mut v_r_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4456_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(v_xs_4451_, v_ys_4452_, v_hsz_4453_, v_x_4454_, v_x_4455_);
    crate::leanh::lean_dec_ref(v_ys_4452_);
    crate::leanh::lean_dec_ref(v_xs_4451_);
    v_r_4457_ = crate::leanh::lean_box((v_res_4456_) as usize);
    return v_r_4457_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(
    mut v_xs_4458_: *mut crate::leanh::LeanObject,
    mut v_ys_4459_: *mut crate::leanh::LeanObject,
    mut v_hsz_4460_: *mut crate::leanh::LeanObject,
    mut v_x_4461_: *mut crate::leanh::LeanObject,
    mut v_x_4462_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4463_: u8 = 0;
    v___x_4463_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_4458_, v_ys_4459_, v_x_4461_);
    return v___x_4463_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___boxed(
    mut v_xs_4464_: *mut crate::leanh::LeanObject,
    mut v_ys_4465_: *mut crate::leanh::LeanObject,
    mut v_hsz_4466_: *mut crate::leanh::LeanObject,
    mut v_x_4467_: *mut crate::leanh::LeanObject,
    mut v_x_4468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4469_: u8 = 0;
    let mut v_r_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4469_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(v_xs_4464_, v_ys_4465_, v_hsz_4466_, v_x_4467_, v_x_4468_);
    crate::leanh::lean_dec_ref(v_ys_4465_);
    crate::leanh::lean_dec_ref(v_xs_4464_);
    v_r_4470_ = crate::leanh::lean_box((v_res_4469_) as usize);
    return v_r_4470_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(
    mut v_xs_4471_: *mut crate::leanh::LeanObject,
    mut v_ys_4472_: *mut crate::leanh::LeanObject,
    mut v_hsz_4473_: *mut crate::leanh::LeanObject,
    mut v_x_4474_: *mut crate::leanh::LeanObject,
    mut v_x_4475_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4476_: u8 = 0;
    v___x_4476_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_4471_, v_ys_4472_, v_x_4474_);
    return v___x_4476_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___boxed(
    mut v_xs_4477_: *mut crate::leanh::LeanObject,
    mut v_ys_4478_: *mut crate::leanh::LeanObject,
    mut v_hsz_4479_: *mut crate::leanh::LeanObject,
    mut v_x_4480_: *mut crate::leanh::LeanObject,
    mut v_x_4481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4482_: u8 = 0;
    let mut v_r_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4482_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(v_xs_4477_, v_ys_4478_, v_hsz_4479_, v_x_4480_, v_x_4481_);
    crate::leanh::lean_dec_ref(v_ys_4478_);
    crate::leanh::lean_dec_ref(v_xs_4477_);
    v_r_4483_ = crate::leanh::lean_box((v_res_4482_) as usize);
    return v_r_4483_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(
    mut v_k_4486_: *mut crate::leanh::LeanObject,
    mut v_x_4487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4492_: u8 = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4487_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_4486_);
                    v___x_4488_ = crate::leanh::lean_box(0);
                    return v___x_4488_;
                } else {
                    v_val_4489_ = crate::leanh::lean_ctor_get(v_x_4487_, 0);
                    v_isSharedCheck_4500_ = (!crate::leanh::lean_is_exclusive(v_x_4487_)) as u8;
                    if v_isSharedCheck_4500_ == 0 {
                        v___x_4491_ = v_x_4487_;
                        v_isShared_4492_ = v_isSharedCheck_4500_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4489_);
                        crate::leanh::lean_dec(v_x_4487_);
                        v___x_4491_ = crate::leanh::lean_box(0);
                        v_isShared_4492_ = v_isSharedCheck_4500_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4493_ = l_Lean_JsonNumber_fromInt(v_val_4489_);
                if v_isShared_4492_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4491_, 2);
                    crate::leanh::lean_ctor_set(v___x_4491_, 0, v___x_4493_);
                    v___x_4495_ = v___x_4491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4499_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4493_);
                    v___x_4495_ = v_reuseFailAlloc_4499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4496_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4496_, 0, v_k_4486_);
                crate::leanh::lean_ctor_set(v___x_4496_, 1, v___x_4495_);
                v___x_4497_ = crate::leanh::lean_box(0);
                v___x_4498_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4498_, 0, v___x_4496_);
                crate::leanh::lean_ctor_set(v___x_4498_, 1, v___x_4497_);
                return v___x_4498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(
    mut v_k_4501_: *mut crate::leanh::LeanObject,
    mut v_x_4502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4502_) == 0 {
        let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4501_);
        v___x_4503_ = crate::leanh::lean_box(0);
        return v___x_4503_;
    } else {
        let mut v_val_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4506_: u8 = 0;
        let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4504_ = crate::leanh::lean_ctor_get(v_x_4502_, 0);
        v___x_4505_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
        v___x_4506_ = (crate::leanh::lean_unbox(v_val_4504_) as u8);
        crate::leanh::lean_ctor_set_uint8(v___x_4505_, 0 as u32, v___x_4506_);
        v___x_4507_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4507_, 0, v_k_4501_);
        crate::leanh::lean_ctor_set(v___x_4507_, 1, v___x_4505_);
        v___x_4508_ = crate::leanh::lean_box(0);
        v___x_4509_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4509_, 0, v___x_4507_);
        crate::leanh::lean_ctor_set(v___x_4509_, 1, v___x_4508_);
        return v___x_4509_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1___boxed(
    mut v_k_4510_: *mut crate::leanh::LeanObject,
    mut v_x_4511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4512_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(
            v_k_4510_, v_x_4511_,
        );
    crate::leanh::lean_dec(v_x_4511_);
    return v_res_4512_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(
    mut v_k_4513_: *mut crate::leanh::LeanObject,
    mut v_x_4514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4514_) == 0 {
        let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4513_);
        v___x_4515_ = crate::leanh::lean_box(0);
        return v___x_4515_;
    } else {
        let mut v_val_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4516_ = crate::leanh::lean_ctor_get(v_x_4514_, 0);
        crate::leanh::lean_inc(v_val_4516_);
        v___x_4517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4517_, 0, v_k_4513_);
        crate::leanh::lean_ctor_set(v___x_4517_, 1, v_val_4516_);
        v___x_4518_ = crate::leanh::lean_box(0);
        v___x_4519_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4519_, 0, v___x_4517_);
        crate::leanh::lean_ctor_set(v___x_4519_, 1, v___x_4518_);
        return v___x_4519_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10___boxed(
    mut v_k_4520_: *mut crate::leanh::LeanObject,
    mut v_x_4521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4522_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v_k_4520_, v_x_4521_);
    crate::leanh::lean_dec(v_x_4521_);
    return v_res_4522_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(
    mut v_k_4523_: *mut crate::leanh::LeanObject,
    mut v_x_4524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_s_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4544_: u8 = 0;
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4524_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_4523_);
                    v___x_4530_ = crate::leanh::lean_box(0);
                    return v___x_4530_;
                } else {
                    v_val_4531_ = crate::leanh::lean_ctor_get(v_x_4524_, 0);
                    crate::leanh::lean_inc(v_val_4531_);
                    crate::leanh::lean_dec_ref_known(v_x_4524_, 1);
                    if crate::leanh::lean_obj_tag(v_val_4531_) == 0 {
                        v_i_4532_ = crate::leanh::lean_ctor_get(v_val_4531_, 0);
                        v_isSharedCheck_4540_ =
                            (!crate::leanh::lean_is_exclusive(v_val_4531_)) as u8;
                        if v_isSharedCheck_4540_ == 0 {
                            v___x_4534_ = v_val_4531_;
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_i_4532_);
                            crate::leanh::lean_dec(v_val_4531_);
                            v___x_4534_ = crate::leanh::lean_box(0);
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_s_4541_ = crate::leanh::lean_ctor_get(v_val_4531_, 0);
                        v_isSharedCheck_4548_ =
                            (!crate::leanh::lean_is_exclusive(v_val_4531_)) as u8;
                        if v_isSharedCheck_4548_ == 0 {
                            v___x_4543_ = v_val_4531_;
                            v_isShared_4544_ = v_isSharedCheck_4548_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_s_4541_);
                            crate::leanh::lean_dec(v_val_4531_);
                            v___x_4543_ = crate::leanh::lean_box(0);
                            v_isShared_4544_ = v_isSharedCheck_4548_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4527_, 0, v_k_4523_);
                crate::leanh::lean_ctor_set(v___x_4527_, 1, v___y_4526_);
                v___x_4528_ = crate::leanh::lean_box(0);
                v___x_4529_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4529_, 0, v___x_4527_);
                crate::leanh::lean_ctor_set(v___x_4529_, 1, v___x_4528_);
                return v___x_4529_;
            }
            2 => {
                v___x_4536_ = l_Lean_JsonNumber_fromInt(v_i_4532_);
                if v_isShared_4535_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4534_, 2);
                    crate::leanh::lean_ctor_set(v___x_4534_, 0, v___x_4536_);
                    v___x_4538_ = v___x_4534_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4539_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
                    v___x_4538_ = v_reuseFailAlloc_4539_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_4526_ = v___x_4538_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_4544_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4543_, 3);
                    v___x_4546_ = v___x_4543_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4547_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_s_4541_);
                    v___x_4546_ = v_reuseFailAlloc_4547_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_4526_ = v___x_4546_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(
    mut v_k_4549_: *mut crate::leanh::LeanObject,
    mut v_x_4550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4550_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_4549_);
                    v___x_4551_ = crate::leanh::lean_box(0);
                    return v___x_4551_;
                } else {
                    v_val_4552_ = crate::leanh::lean_ctor_get(v_x_4550_, 0);
                    v_isSharedCheck_4562_ = (!crate::leanh::lean_is_exclusive(v_x_4550_)) as u8;
                    if v_isSharedCheck_4562_ == 0 {
                        v___x_4554_ = v_x_4550_;
                        v_isShared_4555_ = v_isSharedCheck_4562_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4552_);
                        crate::leanh::lean_dec(v_x_4550_);
                        v___x_4554_ = crate::leanh::lean_box(0);
                        v_isShared_4555_ = v_isSharedCheck_4562_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4555_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4554_, 3);
                    v___x_4557_ = v___x_4554_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4561_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_val_4552_);
                    v___x_4557_ = v_reuseFailAlloc_4561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4558_, 0, v_k_4549_);
                crate::leanh::lean_ctor_set(v___x_4558_, 1, v___x_4557_);
                v___x_4559_ = crate::leanh::lean_box(0);
                v___x_4560_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4560_, 0, v___x_4558_);
                crate::leanh::lean_ctor_set(v___x_4560_, 1, v___x_4559_);
                return v___x_4560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(
    mut v_sz_4563_: usize,
    mut v_i_4564_: usize,
    mut v_bs_4565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4566_: u8 = 0;
    let mut v_v_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: usize = 0;
    let mut v___x_4573_: usize = 0;
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4566_ = lean_usize_dec_lt(v_i_4564_, v_sz_4563_);
                if v___x_4566_ == 0 {
                    return v_bs_4565_;
                } else {
                    v_v_4567_ = lean_array_uget(v_bs_4565_, v_i_4564_);
                    v___x_4568_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4569_ = lean_array_uset(v_bs_4565_, v_i_4564_, v___x_4568_);
                    v___x_4576_ = (crate::leanh::lean_unbox(v_v_4567_) as u8);
                    crate::leanh::lean_dec(v_v_4567_);
                    if v___x_4576_ == 0 {
                        v___x_4577_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1,
                        );
                        v___y_4571_ = v___x_4577_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4578_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3,
                        );
                        v___y_4571_ = v___x_4578_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4572_ = 1usize;
                v___x_4573_ = lean_usize_add(v_i_4564_, v___x_4572_);
                crate::leanh::lean_inc(v___y_4571_);
                v___x_4574_ = lean_array_uset(v_bs_x27_4569_, v_i_4564_, v___y_4571_);
                v_i_4564_ = v___x_4573_;
                v_bs_4565_ = v___x_4574_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14___boxed(
    mut v_sz_4579_: *mut crate::leanh::LeanObject,
    mut v_i_4580_: *mut crate::leanh::LeanObject,
    mut v_bs_4581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4582_: usize = 0;
    let mut v_i_boxed_4583_: usize = 0;
    let mut v_res_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4582_ = crate::leanh::lean_unbox_usize(v_sz_4579_);
    crate::leanh::lean_dec(v_sz_4579_);
    v_i_boxed_4583_ = crate::leanh::lean_unbox_usize(v_i_4580_);
    crate::leanh::lean_dec(v_i_4580_);
    v_res_4584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_boxed_4582_, v_i_boxed_4583_, v_bs_4581_);
    return v_res_4584_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(
    mut v_a_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4586_: usize = 0;
    let mut v___x_4587_: usize = 0;
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4586_ = lean_array_size(v_a_4585_);
    v___x_4587_ = 0usize;
    v___x_4588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_4586_, v___x_4587_, v_a_4585_);
    v___x_4589_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4589_, 0, v___x_4588_);
    return v___x_4589_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(
    mut v_k_4590_: *mut crate::leanh::LeanObject,
    mut v_x_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4591_) == 0 {
        let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4590_);
        v___x_4592_ = crate::leanh::lean_box(0);
        return v___x_4592_;
    } else {
        let mut v_val_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4593_ = crate::leanh::lean_ctor_get(v_x_4591_, 0);
        crate::leanh::lean_inc(v_val_4593_);
        crate::leanh::lean_dec_ref_known(v_x_4591_, 1);
        v___x_4594_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(v_val_4593_);
        v___x_4595_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4595_, 0, v_k_4590_);
        crate::leanh::lean_ctor_set(v___x_4595_, 1, v___x_4594_);
        v___x_4596_ = crate::leanh::lean_box(0);
        v___x_4597_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4597_, 0, v___x_4595_);
        crate::leanh::lean_ctor_set(v___x_4597_, 1, v___x_4596_);
        return v___x_4597_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(
    mut v_k_4598_: *mut crate::leanh::LeanObject,
    mut v_x_4599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: u8 = 0;
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4599_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_4598_);
                    v___x_4605_ = crate::leanh::lean_box(0);
                    return v___x_4605_;
                } else {
                    v_val_4606_ = crate::leanh::lean_ctor_get(v_x_4599_, 0);
                    v___x_4607_ = (crate::leanh::lean_unbox(v_val_4606_) as u8);
                    match v___x_4607_ {
                        0 => {
                            v___x_4608_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once), _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
                            v___y_4601_ = v___x_4608_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_4609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once), _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
                            v___y_4601_ = v___x_4609_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v___x_4610_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once), _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
                            v___y_4601_ = v___x_4610_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___x_4611_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once), _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
                            v___y_4601_ = v___x_4611_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_4601_);
                v___x_4602_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4602_, 0, v_k_4598_);
                crate::leanh::lean_ctor_set(v___x_4602_, 1, v___y_4601_);
                v___x_4603_ = crate::leanh::lean_box(0);
                v___x_4604_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4604_, 0, v___x_4602_);
                crate::leanh::lean_ctor_set(v___x_4604_, 1, v___x_4603_);
                return v___x_4604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4___boxed(
    mut v_k_4612_: *mut crate::leanh::LeanObject,
    mut v_x_4613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4614_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v_k_4612_, v_x_4613_);
    crate::leanh::lean_dec(v_x_4613_);
    return v_res_4614_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(
    mut v_sz_4615_: usize,
    mut v_i_4616_: usize,
    mut v_bs_4617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4618_: u8 = 0;
    let mut v_v_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: usize = 0;
    let mut v___x_4624_: usize = 0;
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4618_ = lean_usize_dec_lt(v_i_4616_, v_sz_4615_);
                if v___x_4618_ == 0 {
                    return v_bs_4617_;
                } else {
                    v_v_4619_ = lean_array_uget(v_bs_4617_, v_i_4616_);
                    v___x_4620_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4621_ = lean_array_uset(v_bs_4617_, v_i_4616_, v___x_4620_);
                    v___x_4622_ =
                        l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_v_4619_);
                    v___x_4623_ = 1usize;
                    v___x_4624_ = lean_usize_add(v_i_4616_, v___x_4623_);
                    v___x_4625_ = lean_array_uset(v_bs_x27_4621_, v_i_4616_, v___x_4622_);
                    v_i_4616_ = v___x_4624_;
                    v_bs_4617_ = v___x_4625_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17___boxed(
    mut v_sz_4627_: *mut crate::leanh::LeanObject,
    mut v_i_4628_: *mut crate::leanh::LeanObject,
    mut v_bs_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4630_: usize = 0;
    let mut v_i_boxed_4631_: usize = 0;
    let mut v_res_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4630_ = crate::leanh::lean_unbox_usize(v_sz_4627_);
    crate::leanh::lean_dec(v_sz_4627_);
    v_i_boxed_4631_ = crate::leanh::lean_unbox_usize(v_i_4628_);
    crate::leanh::lean_dec(v_i_4628_);
    v_res_4632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_boxed_4630_, v_i_boxed_4631_, v_bs_4629_);
    return v_res_4632_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(
    mut v_a_4633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4634_: usize = 0;
    let mut v___x_4635_: usize = 0;
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4634_ = lean_array_size(v_a_4633_);
    v___x_4635_ = 0usize;
    v___x_4636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_4634_, v___x_4635_, v_a_4633_);
    v___x_4637_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4637_, 0, v___x_4636_);
    return v___x_4637_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(
    mut v_k_4638_: *mut crate::leanh::LeanObject,
    mut v_x_4639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4639_) == 0 {
        let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4638_);
        v___x_4640_ = crate::leanh::lean_box(0);
        return v___x_4640_;
    } else {
        let mut v_val_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4641_ = crate::leanh::lean_ctor_get(v_x_4639_, 0);
        crate::leanh::lean_inc(v_val_4641_);
        crate::leanh::lean_dec_ref_known(v_x_4639_, 1);
        v___x_4642_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(v_val_4641_);
        v___x_4643_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4643_, 0, v_k_4638_);
        crate::leanh::lean_ctor_set(v___x_4643_, 1, v___x_4642_);
        v___x_4644_ = crate::leanh::lean_box(0);
        v___x_4645_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4645_, 0, v___x_4643_);
        crate::leanh::lean_ctor_set(v___x_4645_, 1, v___x_4644_);
        return v___x_4645_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(
    mut v_sz_4646_: usize,
    mut v_i_4647_: usize,
    mut v_bs_4648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4649_: u8 = 0;
    let mut v_v_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: usize = 0;
    let mut v___x_4656_: usize = 0;
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: u8 = 0;
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4649_ = lean_usize_dec_lt(v_i_4647_, v_sz_4646_);
                if v___x_4649_ == 0 {
                    return v_bs_4648_;
                } else {
                    v_v_4650_ = lean_array_uget(v_bs_4648_, v_i_4647_);
                    v___x_4651_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4652_ = lean_array_uset(v_bs_4648_, v_i_4647_, v___x_4651_);
                    v___x_4659_ = (crate::leanh::lean_unbox(v_v_4650_) as u8);
                    crate::leanh::lean_dec(v_v_4650_);
                    if v___x_4659_ == 0 {
                        v___x_4660_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1,
                        );
                        v___y_4654_ = v___x_4660_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4661_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3,
                        );
                        v___y_4654_ = v___x_4661_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4655_ = 1usize;
                v___x_4656_ = lean_usize_add(v_i_4647_, v___x_4655_);
                crate::leanh::lean_inc(v___y_4654_);
                v___x_4657_ = lean_array_uset(v_bs_x27_4652_, v_i_4647_, v___y_4654_);
                v_i_4647_ = v___x_4656_;
                v_bs_4648_ = v___x_4657_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11___boxed(
    mut v_sz_4662_: *mut crate::leanh::LeanObject,
    mut v_i_4663_: *mut crate::leanh::LeanObject,
    mut v_bs_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4665_: usize = 0;
    let mut v_i_boxed_4666_: usize = 0;
    let mut v_res_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4665_ = crate::leanh::lean_unbox_usize(v_sz_4662_);
    crate::leanh::lean_dec(v_sz_4662_);
    v_i_boxed_4666_ = crate::leanh::lean_unbox_usize(v_i_4663_);
    crate::leanh::lean_dec(v_i_4663_);
    v_res_4667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_boxed_4665_, v_i_boxed_4666_, v_bs_4664_);
    return v_res_4667_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(
    mut v_a_4668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4669_: usize = 0;
    let mut v___x_4670_: usize = 0;
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4669_ = lean_array_size(v_a_4668_);
    v___x_4670_ = 0usize;
    v___x_4671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_4669_, v___x_4670_, v_a_4668_);
    v___x_4672_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4672_, 0, v___x_4671_);
    return v___x_4672_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(
    mut v_k_4673_: *mut crate::leanh::LeanObject,
    mut v_x_4674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4674_) == 0 {
        let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4673_);
        v___x_4675_ = crate::leanh::lean_box(0);
        return v___x_4675_;
    } else {
        let mut v_val_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4676_ = crate::leanh::lean_ctor_get(v_x_4674_, 0);
        crate::leanh::lean_inc(v_val_4676_);
        crate::leanh::lean_dec_ref_known(v_x_4674_, 1);
        v___x_4677_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(v_val_4676_);
        v___x_4678_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4678_, 0, v_k_4673_);
        crate::leanh::lean_ctor_set(v___x_4678_, 1, v___x_4677_);
        v___x_4679_ = crate::leanh::lean_box(0);
        v___x_4680_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4680_, 0, v___x_4678_);
        crate::leanh::lean_ctor_set(v___x_4680_, 1, v___x_4679_);
        return v___x_4680_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(
    mut v_k_4681_: *mut crate::leanh::LeanObject,
    mut v_x_4682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4682_) == 0 {
        let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4681_);
        v___x_4683_ = crate::leanh::lean_box(0);
        return v___x_4683_;
    } else {
        let mut v_val_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4684_ = crate::leanh::lean_ctor_get(v_x_4682_, 0);
        crate::leanh::lean_inc(v_val_4684_);
        crate::leanh::lean_dec_ref_known(v_x_4682_, 1);
        v___x_4685_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_4684_);
        v___x_4686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4686_, 0, v_k_4681_);
        crate::leanh::lean_ctor_set(v___x_4686_, 1, v___x_4685_);
        v___x_4687_ = crate::leanh::lean_box(0);
        v___x_4688_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4688_, 0, v___x_4686_);
        crate::leanh::lean_ctor_set(v___x_4688_, 1, v___x_4687_);
        return v___x_4688_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(
    mut v_x_4689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_range_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_4690_ = crate::leanh::lean_ctor_get(v_x_4689_, 0);
    crate::leanh::lean_inc_ref(v_range_4690_);
    v_fullRange_x3f_4691_ = crate::leanh::lean_ctor_get(v_x_4689_, 1);
    crate::leanh::lean_inc(v_fullRange_x3f_4691_);
    v_severity_x3f_4692_ = crate::leanh::lean_ctor_get(v_x_4689_, 2);
    crate::leanh::lean_inc(v_severity_x3f_4692_);
    v_isSilent_x3f_4693_ = crate::leanh::lean_ctor_get(v_x_4689_, 3);
    crate::leanh::lean_inc(v_isSilent_x3f_4693_);
    v_code_x3f_4694_ = crate::leanh::lean_ctor_get(v_x_4689_, 4);
    crate::leanh::lean_inc(v_code_x3f_4694_);
    v_source_x3f_4695_ = crate::leanh::lean_ctor_get(v_x_4689_, 5);
    crate::leanh::lean_inc(v_source_x3f_4695_);
    v_message_4696_ = crate::leanh::lean_ctor_get(v_x_4689_, 6);
    crate::leanh::lean_inc(v_message_4696_);
    v_tags_x3f_4697_ = crate::leanh::lean_ctor_get(v_x_4689_, 7);
    crate::leanh::lean_inc(v_tags_x3f_4697_);
    v_leanTags_x3f_4698_ = crate::leanh::lean_ctor_get(v_x_4689_, 8);
    crate::leanh::lean_inc(v_leanTags_x3f_4698_);
    v_relatedInformation_x3f_4699_ = crate::leanh::lean_ctor_get(v_x_4689_, 9);
    crate::leanh::lean_inc(v_relatedInformation_x3f_4699_);
    v_data_x3f_4700_ = crate::leanh::lean_ctor_get(v_x_4689_, 10);
    crate::leanh::lean_inc(v_data_x3f_4700_);
    crate::leanh::lean_dec_ref(v_x_4689_);
    v___x_4701_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7;
    v___x_4702_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_4690_);
    v___x_4703_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4703_, 0, v___x_4701_);
    crate::leanh::lean_ctor_set(v___x_4703_, 1, v___x_4702_);
    v___x_4704_ = crate::leanh::lean_box(0);
    v___x_4705_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4705_, 0, v___x_4703_);
    crate::leanh::lean_ctor_set(v___x_4705_, 1, v___x_4704_);
    v___x_4706_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8;
    v___x_4707_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(v___x_4706_, v_fullRange_x3f_4691_);
    v___x_4708_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9;
    v___x_4709_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v___x_4708_, v_severity_x3f_4692_);
    crate::leanh::lean_dec(v_severity_x3f_4692_);
    v___x_4710_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10;
    v___x_4711_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(
            v___x_4710_,
            v_isSilent_x3f_4693_,
        );
    crate::leanh::lean_dec(v_isSilent_x3f_4693_);
    v___x_4712_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11;
    v___x_4713_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(v___x_4712_, v_code_x3f_4694_);
    v___x_4714_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12;
    v___x_4715_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(v___x_4714_, v_source_x3f_4695_);
    v___x_4716_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
    v___x_4717_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4717_, 0, v_message_4696_);
    v___x_4718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4718_, 0, v___x_4716_);
    crate::leanh::lean_ctor_set(v___x_4718_, 1, v___x_4717_);
    v___x_4719_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4719_, 0, v___x_4718_);
    crate::leanh::lean_ctor_set(v___x_4719_, 1, v___x_4704_);
    v___x_4720_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13;
    v___x_4721_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(v___x_4720_, v_tags_x3f_4697_);
    v___x_4722_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14;
    v___x_4723_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(v___x_4722_, v_leanTags_x3f_4698_);
    v___x_4724_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15;
    v___x_4725_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(v___x_4724_, v_relatedInformation_x3f_4699_);
    v___x_4726_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16;
    v___x_4727_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v___x_4726_, v_data_x3f_4700_);
    crate::leanh::lean_dec(v_data_x3f_4700_);
    v___x_4728_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4728_, 0, v___x_4727_);
    crate::leanh::lean_ctor_set(v___x_4728_, 1, v___x_4704_);
    v___x_4729_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4729_, 0, v___x_4725_);
    crate::leanh::lean_ctor_set(v___x_4729_, 1, v___x_4728_);
    v___x_4730_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4730_, 0, v___x_4723_);
    crate::leanh::lean_ctor_set(v___x_4730_, 1, v___x_4729_);
    v___x_4731_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4731_, 0, v___x_4721_);
    crate::leanh::lean_ctor_set(v___x_4731_, 1, v___x_4730_);
    v___x_4732_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4732_, 0, v___x_4719_);
    crate::leanh::lean_ctor_set(v___x_4732_, 1, v___x_4731_);
    v___x_4733_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4733_, 0, v___x_4715_);
    crate::leanh::lean_ctor_set(v___x_4733_, 1, v___x_4732_);
    v___x_4734_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4734_, 0, v___x_4713_);
    crate::leanh::lean_ctor_set(v___x_4734_, 1, v___x_4733_);
    v___x_4735_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4735_, 0, v___x_4711_);
    crate::leanh::lean_ctor_set(v___x_4735_, 1, v___x_4734_);
    v___x_4736_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4709_);
    crate::leanh::lean_ctor_set(v___x_4736_, 1, v___x_4735_);
    v___x_4737_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4737_, 0, v___x_4707_);
    crate::leanh::lean_ctor_set(v___x_4737_, 1, v___x_4736_);
    v___x_4738_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4738_, 0, v___x_4705_);
    crate::leanh::lean_ctor_set(v___x_4738_, 1, v___x_4737_);
    v___x_4739_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2;
    v___x_4740_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_4738_, v___x_4739_);
    v___x_4741_ = l_Lean_Json_mkObj(v___x_4740_);
    crate::leanh::lean_dec(v___x_4740_);
    return v___x_4741_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(
    mut v_sz_4742_: usize,
    mut v_i_4743_: usize,
    mut v_bs_4744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4745_: u8 = 0;
    let mut v_v_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: usize = 0;
    let mut v___x_4751_: usize = 0;
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4745_ = lean_usize_dec_lt(v_i_4743_, v_sz_4742_);
                if v___x_4745_ == 0 {
                    return v_bs_4744_;
                } else {
                    v_v_4746_ = lean_array_uget(v_bs_4744_, v_i_4743_);
                    v___x_4747_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4748_ = lean_array_uset(v_bs_4744_, v_i_4743_, v___x_4747_);
                    v___x_4749_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(v_v_4746_);
                    v___x_4750_ = 1usize;
                    v___x_4751_ = lean_usize_add(v_i_4743_, v___x_4750_);
                    v___x_4752_ = lean_array_uset(v_bs_x27_4748_, v_i_4743_, v___x_4749_);
                    v_i_4743_ = v___x_4751_;
                    v_bs_4744_ = v___x_4752_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3___boxed(
    mut v_sz_4754_: *mut crate::leanh::LeanObject,
    mut v_i_4755_: *mut crate::leanh::LeanObject,
    mut v_bs_4756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4757_: usize = 0;
    let mut v_i_boxed_4758_: usize = 0;
    let mut v_res_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4757_ = crate::leanh::lean_unbox_usize(v_sz_4754_);
    crate::leanh::lean_dec(v_sz_4754_);
    v_i_boxed_4758_ = crate::leanh::lean_unbox_usize(v_i_4755_);
    crate::leanh::lean_dec(v_i_4755_);
    v_res_4759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_boxed_4757_, v_i_boxed_4758_, v_bs_4756_);
    return v_res_4759_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(
    mut v_a_4760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4761_: usize = 0;
    let mut v___x_4762_: usize = 0;
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4761_ = lean_array_size(v_a_4760_);
    v___x_4762_ = 0usize;
    v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_4761_, v___x_4762_, v_a_4760_);
    v___x_4764_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4764_, 0, v___x_4763_);
    return v___x_4764_;
}
pub unsafe fn l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(
    mut v_x_4769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isIncremental_x3f_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_4770_ = crate::leanh::lean_ctor_get(v_x_4769_, 0);
    crate::leanh::lean_inc_ref(v_uri_4770_);
    v_version_x3f_4771_ = crate::leanh::lean_ctor_get(v_x_4769_, 1);
    crate::leanh::lean_inc(v_version_x3f_4771_);
    v_isIncremental_x3f_4772_ = crate::leanh::lean_ctor_get(v_x_4769_, 2);
    crate::leanh::lean_inc(v_isIncremental_x3f_4772_);
    v_diagnostics_4773_ = crate::leanh::lean_ctor_get(v_x_4769_, 3);
    crate::leanh::lean_inc_ref(v_diagnostics_4773_);
    crate::leanh::lean_dec_ref(v_x_4769_);
    v___x_4774_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0;
    v___x_4775_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4775_, 0, v_uri_4770_);
    v___x_4776_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4776_, 0, v___x_4774_);
    crate::leanh::lean_ctor_set(v___x_4776_, 1, v___x_4775_);
    v___x_4777_ = crate::leanh::lean_box(0);
    v___x_4778_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4778_, 0, v___x_4776_);
    crate::leanh::lean_ctor_set(v___x_4778_, 1, v___x_4777_);
    v___x_4779_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1;
    v___x_4780_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(
            v___x_4779_,
            v_version_x3f_4771_,
        );
    v___x_4781_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2;
    v___x_4782_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(
            v___x_4781_,
            v_isIncremental_x3f_4772_,
        );
    crate::leanh::lean_dec(v_isIncremental_x3f_4772_);
    v___x_4783_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3;
    v___x_4784_ =
        l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(
            v_diagnostics_4773_,
        );
    v___x_4785_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4785_, 0, v___x_4783_);
    crate::leanh::lean_ctor_set(v___x_4785_, 1, v___x_4784_);
    v___x_4786_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4786_, 0, v___x_4785_);
    crate::leanh::lean_ctor_set(v___x_4786_, 1, v___x_4777_);
    v___x_4787_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4787_, 0, v___x_4786_);
    crate::leanh::lean_ctor_set(v___x_4787_, 1, v___x_4777_);
    v___x_4788_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4788_, 0, v___x_4782_);
    crate::leanh::lean_ctor_set(v___x_4788_, 1, v___x_4787_);
    v___x_4789_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4789_, 0, v___x_4780_);
    crate::leanh::lean_ctor_set(v___x_4789_, 1, v___x_4788_);
    v___x_4790_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4790_, 0, v___x_4778_);
    crate::leanh::lean_ctor_set(v___x_4790_, 1, v___x_4789_);
    v___x_4791_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2;
    v___x_4792_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_4790_, v___x_4791_);
    v___x_4793_ = l_Lean_Json_mkObj(v___x_4792_);
    crate::leanh::lean_dec(v___x_4792_);
    return v___x_4793_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(
    mut v_x_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4804_: u8 = 0;
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut v_a_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4812_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4798_) == 0 {
                    v___x_4799_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0;
                    return v___x_4799_;
                } else {
                    v___x_4800_ = l_Lean_Json_getBool_x3f(v_x_4798_);
                    if crate::leanh::lean_obj_tag(v___x_4800_) == 0 {
                        v_a_4801_ = crate::leanh::lean_ctor_get(v___x_4800_, 0);
                        v_isSharedCheck_4808_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4800_)) as u8;
                        if v_isSharedCheck_4808_ == 0 {
                            v___x_4803_ = v___x_4800_;
                            v_isShared_4804_ = v_isSharedCheck_4808_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4801_);
                            crate::leanh::lean_dec(v___x_4800_);
                            v___x_4803_ = crate::leanh::lean_box(0);
                            v_isShared_4804_ = v_isSharedCheck_4808_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4809_ = crate::leanh::lean_ctor_get(v___x_4800_, 0);
                        v_isSharedCheck_4817_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4800_)) as u8;
                        if v_isSharedCheck_4817_ == 0 {
                            v___x_4811_ = v___x_4800_;
                            v_isShared_4812_ = v_isSharedCheck_4817_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4809_);
                            crate::leanh::lean_dec(v___x_4800_);
                            v___x_4811_ = crate::leanh::lean_box(0);
                            v_isShared_4812_ = v_isSharedCheck_4817_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4804_ == 0 {
                    v___x_4806_ = v___x_4803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4807_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
                    v___x_4806_ = v_reuseFailAlloc_4807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4806_;
            }
            3 => {
                v___x_4813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4813_, 0, v_a_4809_);
                if v_isShared_4812_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4811_, 0, v___x_4813_);
                    v___x_4815_ = v___x_4811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
                    v___x_4815_ = v_reuseFailAlloc_4816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___boxed(
    mut v_x_4818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4819_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v_x_4818_);
    crate::leanh::lean_dec(v_x_4818_);
    return v_res_4819_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(
    mut v_j_4820_: *mut crate::leanh::LeanObject,
    mut v_k_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4822_ = l_Lean_Json_getObjValD(v_j_4820_, v_k_4821_);
    v___x_4823_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v___x_4822_);
    crate::leanh::lean_dec(v___x_4822_);
    return v___x_4823_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(
    mut v_j_4824_: *mut crate::leanh::LeanObject,
    mut v_k_4825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4826_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_j_4824_, v_k_4825_);
    crate::leanh::lean_dec_ref(v_k_4825_);
    return v_res_4826_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(
    mut v_x_4829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4835_: u8 = 0;
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut v_a_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4843_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4829_) == 0 {
                    v___x_4830_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0;
                    return v___x_4830_;
                } else {
                    v___x_4831_ = l_Lean_Json_getInt_x3f(v_x_4829_);
                    if crate::leanh::lean_obj_tag(v___x_4831_) == 0 {
                        v_a_4832_ = crate::leanh::lean_ctor_get(v___x_4831_, 0);
                        v_isSharedCheck_4839_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4831_)) as u8;
                        if v_isSharedCheck_4839_ == 0 {
                            v___x_4834_ = v___x_4831_;
                            v_isShared_4835_ = v_isSharedCheck_4839_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4832_);
                            crate::leanh::lean_dec(v___x_4831_);
                            v___x_4834_ = crate::leanh::lean_box(0);
                            v_isShared_4835_ = v_isSharedCheck_4839_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4840_ = crate::leanh::lean_ctor_get(v___x_4831_, 0);
                        v_isSharedCheck_4848_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4831_)) as u8;
                        if v_isSharedCheck_4848_ == 0 {
                            v___x_4842_ = v___x_4831_;
                            v_isShared_4843_ = v_isSharedCheck_4848_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4840_);
                            crate::leanh::lean_dec(v___x_4831_);
                            v___x_4842_ = crate::leanh::lean_box(0);
                            v_isShared_4843_ = v_isSharedCheck_4848_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4835_ == 0 {
                    v___x_4837_ = v___x_4834_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4838_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
                    v___x_4837_ = v_reuseFailAlloc_4838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4837_;
            }
            3 => {
                v___x_4844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4844_, 0, v_a_4840_);
                if v_isShared_4843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4842_, 0, v___x_4844_);
                    v___x_4846_ = v___x_4842_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4847_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4844_);
                    v___x_4846_ = v_reuseFailAlloc_4847_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(
    mut v_j_4849_: *mut crate::leanh::LeanObject,
    mut v_k_4850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4851_ = l_Lean_Json_getObjValD(v_j_4849_, v_k_4850_);
    v___x_4852_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(v___x_4851_);
    return v___x_4852_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(
    mut v_j_4853_: *mut crate::leanh::LeanObject,
    mut v_k_4854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4855_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_j_4853_, v_k_4854_);
    crate::leanh::lean_dec_ref(v_k_4854_);
    return v_res_4855_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(
    mut v_x_4858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4858_) == 0 {
        let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4859_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0;
        return v___x_4859_;
    } else {
        let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4860_, 0, v_x_4858_);
        v___x_4861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4861_, 0, v___x_4860_);
        return v___x_4861_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(
    mut v_j_4862_: *mut crate::leanh::LeanObject,
    mut v_k_4863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4864_ = l_Lean_Json_getObjValD(v_j_4862_, v_k_4863_);
    v___x_4865_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(v___x_4864_);
    return v___x_4865_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14___boxed(
    mut v_j_4866_: *mut crate::leanh::LeanObject,
    mut v_k_4867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4868_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_j_4866_, v_k_4867_);
    crate::leanh::lean_dec_ref(v_k_4867_);
    return v_res_4868_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(
    mut v_sz_4871_: usize,
    mut v_i_4872_: usize,
    mut v_bs_4873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u8 = 0;
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: u8 = 0;
    let mut v___x_4885_: usize = 0;
    let mut v___x_4886_: usize = 0;
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: u8 = 0;
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: u8 = 0;
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4876_ = lean_usize_dec_lt(v_i_4872_, v_sz_4871_);
                if v___x_4876_ == 0 {
                    v___x_4877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4877_, 0, v_bs_4873_);
                    return v___x_4877_;
                } else {
                    v_v_4878_ = lean_array_uget_borrowed(v_bs_4873_, v_i_4872_);
                    crate::leanh::lean_inc(v_v_4878_);
                    v___x_4879_ = l_Lean_Json_getNat_x3f(v_v_4878_);
                    if crate::leanh::lean_obj_tag(v___x_4879_) == 1 {
                        v_a_4880_ = crate::leanh::lean_ctor_get(v___x_4879_, 0);
                        crate::leanh::lean_inc(v_a_4880_);
                        crate::leanh::lean_dec_ref_known(v___x_4879_, 1);
                        v___x_4881_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4882_ = lean_array_uset(v_bs_4873_, v_i_4872_, v___x_4881_);
                        v___x_4890_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4891_ = lean_nat_dec_eq(v_a_4880_, v___x_4890_);
                        if v___x_4891_ == 0 {
                            v___x_4892_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_4893_ = lean_nat_dec_eq(v_a_4880_, v___x_4892_);
                            crate::leanh::lean_dec(v_a_4880_);
                            if v___x_4893_ == 0 {
                                crate::leanh::lean_dec_ref(v_bs_x27_4882_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4894_ = 1;
                                v_a_4884_ = v___x_4894_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4880_);
                            v___x_4895_ = 0;
                            v_a_4884_ = v___x_4895_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4879_);
                        crate::leanh::lean_dec_ref(v_bs_4873_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0;
                return v___x_4875_;
            }
            2 => {
                v___x_4885_ = 1usize;
                v___x_4886_ = lean_usize_add(v_i_4872_, v___x_4885_);
                v___x_4887_ = crate::leanh::lean_box((v_a_4884_) as usize);
                v___x_4888_ = lean_array_uset(v_bs_x27_4882_, v_i_4872_, v___x_4887_);
                v_i_4872_ = v___x_4886_;
                v_bs_4873_ = v___x_4888_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___boxed(
    mut v_sz_4896_: *mut crate::leanh::LeanObject,
    mut v_i_4897_: *mut crate::leanh::LeanObject,
    mut v_bs_4898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4899_: usize = 0;
    let mut v_i_boxed_4900_: usize = 0;
    let mut v_res_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4899_ = crate::leanh::lean_unbox_usize(v_sz_4896_);
    crate::leanh::lean_dec(v_sz_4896_);
    v_i_boxed_4900_ = crate::leanh::lean_unbox_usize(v_i_4897_);
    crate::leanh::lean_dec(v_i_4897_);
    v_res_4901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_boxed_4899_, v_i_boxed_4900_, v_bs_4898_);
    return v_res_4901_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(
    mut v_x_4903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4903_) == 4 {
        let mut v_elems_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4905_: usize = 0;
        let mut v___x_4906_: usize = 0;
        let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_4904_ = crate::leanh::lean_ctor_get(v_x_4903_, 0);
        crate::leanh::lean_inc_ref(v_elems_4904_);
        crate::leanh::lean_dec_ref_known(v_x_4903_, 1);
        v_sz_4905_ = lean_array_size(v_elems_4904_);
        v___x_4906_ = 0usize;
        v___x_4907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_4905_, v___x_4906_, v_elems_4904_);
        return v___x_4907_;
    } else {
        let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4908_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0;
        v___x_4909_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_4910_ = l_Lean_Json_pretty(v_x_4903_, v___x_4909_);
        v___x_4911_ = lean_string_append(v___x_4908_, v___x_4910_);
        crate::leanh::lean_dec_ref(v___x_4910_);
        v___x_4912_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
        v___x_4913_ = lean_string_append(v___x_4911_, v___x_4912_);
        v___x_4914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4914_, 0, v___x_4913_);
        return v___x_4914_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(
    mut v_x_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4923_: u8 = 0;
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4927_: u8 = 0;
    let mut v_a_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4931_: u8 = 0;
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4917_) == 0 {
                    v___x_4918_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0;
                    return v___x_4918_;
                } else {
                    v___x_4919_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(v_x_4917_);
                    if crate::leanh::lean_obj_tag(v___x_4919_) == 0 {
                        v_a_4920_ = crate::leanh::lean_ctor_get(v___x_4919_, 0);
                        v_isSharedCheck_4927_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4919_)) as u8;
                        if v_isSharedCheck_4927_ == 0 {
                            v___x_4922_ = v___x_4919_;
                            v_isShared_4923_ = v_isSharedCheck_4927_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4920_);
                            crate::leanh::lean_dec(v___x_4919_);
                            v___x_4922_ = crate::leanh::lean_box(0);
                            v_isShared_4923_ = v_isSharedCheck_4927_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4928_ = crate::leanh::lean_ctor_get(v___x_4919_, 0);
                        v_isSharedCheck_4936_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4919_)) as u8;
                        if v_isSharedCheck_4936_ == 0 {
                            v___x_4930_ = v___x_4919_;
                            v_isShared_4931_ = v_isSharedCheck_4936_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4928_);
                            crate::leanh::lean_dec(v___x_4919_);
                            v___x_4930_ = crate::leanh::lean_box(0);
                            v_isShared_4931_ = v_isSharedCheck_4936_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4923_ == 0 {
                    v___x_4925_ = v___x_4922_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
                    v___x_4925_ = v_reuseFailAlloc_4926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4925_;
            }
            3 => {
                v___x_4932_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4932_, 0, v_a_4928_);
                if v_isShared_4931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4930_, 0, v___x_4932_);
                    v___x_4934_ = v___x_4930_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
                    v___x_4934_ = v_reuseFailAlloc_4935_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(
    mut v_j_4937_: *mut crate::leanh::LeanObject,
    mut v_k_4938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4939_ = l_Lean_Json_getObjValD(v_j_4937_, v_k_4938_);
    v___x_4940_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(v___x_4939_);
    return v___x_4940_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12___boxed(
    mut v_j_4941_: *mut crate::leanh::LeanObject,
    mut v_k_4942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4943_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_j_4941_, v_k_4942_);
    crate::leanh::lean_dec_ref(v_k_4942_);
    return v_res_4943_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(
    mut v_x_4946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: u8 = 0;
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4946_) == 0 {
                    v___x_4960_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0;
                    return v___x_4960_;
                } else {
                    match crate::leanh::lean_obj_tag(v_x_4946_) {
                        2 => {
                            v_n_4961_ = crate::leanh::lean_ctor_get(v_x_4946_, 0);
                            v_mantissa_4962_ = crate::leanh::lean_ctor_get(v_n_4961_, 0);
                            v_exponent_4963_ = crate::leanh::lean_ctor_get(v_n_4961_, 1);
                            v___x_4964_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4965_ = lean_nat_dec_eq(v_exponent_4963_, v___x_4964_);
                            if v___x_4965_ == 0 {
                                v_j_4952_ = v_x_4946_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_mantissa_4962_);
                                crate::leanh::lean_dec_ref_known(v_x_4946_, 1);
                                v___x_4966_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4966_, 0, v_mantissa_4962_);
                                v_a_4948_ = v___x_4966_;
                                state = 1;
                                continue;
                            }
                        }
                        3 => {
                            v_s_4967_ = crate::leanh::lean_ctor_get(v_x_4946_, 0);
                            crate::leanh::lean_inc_ref(v_s_4967_);
                            crate::leanh::lean_dec_ref_known(v_x_4946_, 1);
                            v___x_4968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4968_, 0, v_s_4967_);
                            v_a_4948_ = v___x_4968_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_j_4952_ = v_x_4946_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4949_, 0, v_a_4948_);
                v___x_4950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4950_, 0, v___x_4949_);
                return v___x_4950_;
            }
            2 => {
                v___x_4953_ = l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0;
                v___x_4954_ = crate::leanh::lean_unsigned_to_nat(80);
                v___x_4955_ = l_Lean_Json_pretty(v_j_4952_, v___x_4954_);
                v___x_4956_ = lean_string_append(v___x_4953_, v___x_4955_);
                crate::leanh::lean_dec_ref(v___x_4955_);
                v___x_4957_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
                v___x_4958_ = lean_string_append(v___x_4956_, v___x_4957_);
                v___x_4959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4959_, 0, v___x_4958_);
                return v___x_4959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(
    mut v_j_4969_: *mut crate::leanh::LeanObject,
    mut v_k_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4971_ = l_Lean_Json_getObjValD(v_j_4969_, v_k_4970_);
    v___x_4972_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(v___x_4971_);
    return v___x_4972_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9___boxed(
    mut v_j_4973_: *mut crate::leanh::LeanObject,
    mut v_k_4974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4975_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_j_4973_, v_k_4974_);
    crate::leanh::lean_dec_ref(v_k_4974_);
    return v_res_4975_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(
    mut v_j_4976_: *mut crate::leanh::LeanObject,
    mut v_k_4977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4978_ = l_Lean_Json_getObjValD(v_j_4976_, v_k_4977_);
    v___x_4979_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4978_);
    return v___x_4979_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6___boxed(
    mut v_j_4980_: *mut crate::leanh::LeanObject,
    mut v_k_4981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4982_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_j_4980_, v_k_4981_);
    crate::leanh::lean_dec_ref(v_k_4981_);
    return v_res_4982_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(
    mut v_sz_4985_: usize,
    mut v_i_4986_: usize,
    mut v_bs_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u8 = 0;
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4998_: u8 = 0;
    let mut v___x_4999_: usize = 0;
    let mut v___x_5000_: usize = 0;
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: u8 = 0;
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: u8 = 0;
    let mut v___x_5008_: u8 = 0;
    let mut v___x_5009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4990_ = lean_usize_dec_lt(v_i_4986_, v_sz_4985_);
                if v___x_4990_ == 0 {
                    v___x_4991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4991_, 0, v_bs_4987_);
                    return v___x_4991_;
                } else {
                    v_v_4992_ = lean_array_uget_borrowed(v_bs_4987_, v_i_4986_);
                    crate::leanh::lean_inc(v_v_4992_);
                    v___x_4993_ = l_Lean_Json_getNat_x3f(v_v_4992_);
                    if crate::leanh::lean_obj_tag(v___x_4993_) == 1 {
                        v_a_4994_ = crate::leanh::lean_ctor_get(v___x_4993_, 0);
                        crate::leanh::lean_inc(v_a_4994_);
                        crate::leanh::lean_dec_ref_known(v___x_4993_, 1);
                        v___x_4995_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4996_ = lean_array_uset(v_bs_4987_, v_i_4986_, v___x_4995_);
                        v___x_5004_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5005_ = lean_nat_dec_eq(v_a_4994_, v___x_5004_);
                        if v___x_5005_ == 0 {
                            v___x_5006_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_5007_ = lean_nat_dec_eq(v_a_4994_, v___x_5006_);
                            crate::leanh::lean_dec(v_a_4994_);
                            if v___x_5007_ == 0 {
                                crate::leanh::lean_dec_ref(v_bs_x27_4996_);
                                state = 1;
                                continue;
                            } else {
                                v___x_5008_ = 1;
                                v_a_4998_ = v___x_5008_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4994_);
                            v___x_5009_ = 0;
                            v_a_4998_ = v___x_5009_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4993_);
                        crate::leanh::lean_dec_ref(v_bs_4987_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0;
                return v___x_4989_;
            }
            2 => {
                v___x_4999_ = 1usize;
                v___x_5000_ = lean_usize_add(v_i_4986_, v___x_4999_);
                v___x_5001_ = crate::leanh::lean_box((v_a_4998_) as usize);
                v___x_5002_ = lean_array_uset(v_bs_x27_4996_, v_i_4986_, v___x_5001_);
                v_i_4986_ = v___x_5000_;
                v_bs_4987_ = v___x_5002_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___boxed(
    mut v_sz_5010_: *mut crate::leanh::LeanObject,
    mut v_i_5011_: *mut crate::leanh::LeanObject,
    mut v_bs_5012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5013_: usize = 0;
    let mut v_i_boxed_5014_: usize = 0;
    let mut v_res_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5013_ = crate::leanh::lean_unbox_usize(v_sz_5010_);
    crate::leanh::lean_dec(v_sz_5010_);
    v_i_boxed_5014_ = crate::leanh::lean_unbox_usize(v_i_5011_);
    crate::leanh::lean_dec(v_i_5011_);
    v_res_5015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_boxed_5013_, v_i_boxed_5014_, v_bs_5012_);
    return v_res_5015_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(
    mut v_x_5016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5016_) == 4 {
        let mut v_elems_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5018_: usize = 0;
        let mut v___x_5019_: usize = 0;
        let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_5017_ = crate::leanh::lean_ctor_get(v_x_5016_, 0);
        crate::leanh::lean_inc_ref(v_elems_5017_);
        crate::leanh::lean_dec_ref_known(v_x_5016_, 1);
        v_sz_5018_ = lean_array_size(v_elems_5017_);
        v___x_5019_ = 0usize;
        v___x_5020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_5018_, v___x_5019_, v_elems_5017_);
        return v___x_5020_;
    } else {
        let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5021_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0;
        v___x_5022_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_5023_ = l_Lean_Json_pretty(v_x_5016_, v___x_5022_);
        v___x_5024_ = lean_string_append(v___x_5021_, v___x_5023_);
        crate::leanh::lean_dec_ref(v___x_5023_);
        v___x_5025_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
        v___x_5026_ = lean_string_append(v___x_5024_, v___x_5025_);
        v___x_5027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5027_, 0, v___x_5026_);
        return v___x_5027_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(
    mut v_x_5030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5036_: u8 = 0;
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5040_: u8 = 0;
    let mut v_a_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5030_) == 0 {
                    v___x_5031_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0;
                    return v___x_5031_;
                } else {
                    v___x_5032_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(v_x_5030_);
                    if crate::leanh::lean_obj_tag(v___x_5032_) == 0 {
                        v_a_5033_ = crate::leanh::lean_ctor_get(v___x_5032_, 0);
                        v_isSharedCheck_5040_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5040_ == 0 {
                            v___x_5035_ = v___x_5032_;
                            v_isShared_5036_ = v_isSharedCheck_5040_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5033_);
                            crate::leanh::lean_dec(v___x_5032_);
                            v___x_5035_ = crate::leanh::lean_box(0);
                            v_isShared_5036_ = v_isSharedCheck_5040_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5041_ = crate::leanh::lean_ctor_get(v___x_5032_, 0);
                        v_isSharedCheck_5049_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5049_ == 0 {
                            v___x_5043_ = v___x_5032_;
                            v_isShared_5044_ = v_isSharedCheck_5049_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5041_);
                            crate::leanh::lean_dec(v___x_5032_);
                            v___x_5043_ = crate::leanh::lean_box(0);
                            v_isShared_5044_ = v_isSharedCheck_5049_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5036_ == 0 {
                    v___x_5038_ = v___x_5035_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
                    v___x_5038_ = v_reuseFailAlloc_5039_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5038_;
            }
            3 => {
                v___x_5045_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5045_, 0, v_a_5041_);
                if v_isShared_5044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5043_, 0, v___x_5045_);
                    v___x_5047_ = v___x_5043_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5045_);
                    v___x_5047_ = v_reuseFailAlloc_5048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(
    mut v_j_5050_: *mut crate::leanh::LeanObject,
    mut v_k_5051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Lean_Json_getObjValD(v_j_5050_, v_k_5051_);
    v___x_5053_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(v___x_5052_);
    return v___x_5053_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11___boxed(
    mut v_j_5054_: *mut crate::leanh::LeanObject,
    mut v_k_5055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5056_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_j_5054_, v_k_5055_);
    crate::leanh::lean_dec_ref(v_k_5055_);
    return v_res_5056_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(
    mut v_x_5059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5069_: u8 = 0;
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: u8 = 0;
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: u8 = 0;
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: u8 = 0;
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: u8 = 0;
    let mut v___x_5084_: u8 = 0;
    let mut v___x_5085_: u8 = 0;
    let mut v___x_5086_: u8 = 0;
    let mut v___x_5087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5059_) == 0 {
                    v___x_5073_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0;
                    return v___x_5073_;
                } else {
                    crate::leanh::lean_inc(v_x_5059_);
                    v___x_5074_ = l_Lean_Json_getNat_x3f(v_x_5059_);
                    if crate::leanh::lean_obj_tag(v___x_5074_) == 1 {
                        v_a_5075_ = crate::leanh::lean_ctor_get(v___x_5074_, 0);
                        crate::leanh::lean_inc(v_a_5075_);
                        crate::leanh::lean_dec_ref_known(v___x_5074_, 1);
                        v___x_5076_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5077_ = lean_nat_dec_eq(v_a_5075_, v___x_5076_);
                        if v___x_5077_ == 0 {
                            v___x_5078_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_5079_ = lean_nat_dec_eq(v_a_5075_, v___x_5078_);
                            if v___x_5079_ == 0 {
                                v___x_5080_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_5081_ = lean_nat_dec_eq(v_a_5075_, v___x_5080_);
                                if v___x_5081_ == 0 {
                                    v___x_5082_ = crate::leanh::lean_unsigned_to_nat(4);
                                    v___x_5083_ = lean_nat_dec_eq(v_a_5075_, v___x_5082_);
                                    crate::leanh::lean_dec(v_a_5075_);
                                    if v___x_5083_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_x_5059_);
                                        v___x_5084_ = 3;
                                        v_a_5069_ = v___x_5084_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5075_);
                                    crate::leanh::lean_dec(v_x_5059_);
                                    v___x_5085_ = 2;
                                    v_a_5069_ = v___x_5085_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5075_);
                                crate::leanh::lean_dec(v_x_5059_);
                                v___x_5086_ = 1;
                                v_a_5069_ = v___x_5086_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5075_);
                            crate::leanh::lean_dec(v_x_5059_);
                            v___x_5087_ = 0;
                            v_a_5069_ = v___x_5087_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5074_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5061_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0;
                v___x_5062_ = crate::leanh::lean_unsigned_to_nat(80);
                v___x_5063_ = l_Lean_Json_pretty(v_x_5059_, v___x_5062_);
                v___x_5064_ = lean_string_append(v___x_5061_, v___x_5063_);
                crate::leanh::lean_dec_ref(v___x_5063_);
                v___x_5065_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
                v___x_5066_ = lean_string_append(v___x_5064_, v___x_5065_);
                v___x_5067_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5067_, 0, v___x_5066_);
                return v___x_5067_;
            }
            2 => {
                v___x_5070_ = crate::leanh::lean_box((v_a_5069_) as usize);
                v___x_5071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5071_, 0, v___x_5070_);
                v___x_5072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5072_, 0, v___x_5071_);
                return v___x_5072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(
    mut v_j_5088_: *mut crate::leanh::LeanObject,
    mut v_k_5089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5090_ = l_Lean_Json_getObjValD(v_j_5088_, v_k_5089_);
    v___x_5091_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(v___x_5090_);
    return v___x_5091_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8___boxed(
    mut v_j_5092_: *mut crate::leanh::LeanObject,
    mut v_k_5093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5094_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_j_5092_, v_k_5093_);
    crate::leanh::lean_dec_ref(v_k_5093_);
    return v_res_5094_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(
    mut v_x_5097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v_a_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5111_: u8 = 0;
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5097_) == 0 {
                    v___x_5098_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0;
                    return v___x_5098_;
                } else {
                    v___x_5099_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_5097_);
                    if crate::leanh::lean_obj_tag(v___x_5099_) == 0 {
                        v_a_5100_ = crate::leanh::lean_ctor_get(v___x_5099_, 0);
                        v_isSharedCheck_5107_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5099_)) as u8;
                        if v_isSharedCheck_5107_ == 0 {
                            v___x_5102_ = v___x_5099_;
                            v_isShared_5103_ = v_isSharedCheck_5107_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5100_);
                            crate::leanh::lean_dec(v___x_5099_);
                            v___x_5102_ = crate::leanh::lean_box(0);
                            v_isShared_5103_ = v_isSharedCheck_5107_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5108_ = crate::leanh::lean_ctor_get(v___x_5099_, 0);
                        v_isSharedCheck_5116_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5099_)) as u8;
                        if v_isSharedCheck_5116_ == 0 {
                            v___x_5110_ = v___x_5099_;
                            v_isShared_5111_ = v_isSharedCheck_5116_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5108_);
                            crate::leanh::lean_dec(v___x_5099_);
                            v___x_5110_ = crate::leanh::lean_box(0);
                            v_isShared_5111_ = v_isSharedCheck_5116_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5103_ == 0 {
                    v___x_5105_ = v___x_5102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5106_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5105_;
            }
            3 => {
                v___x_5112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5112_, 0, v_a_5108_);
                if v_isShared_5111_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5110_, 0, v___x_5112_);
                    v___x_5114_ = v___x_5110_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5115_, 0, v___x_5112_);
                    v___x_5114_ = v_reuseFailAlloc_5115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(
    mut v_j_5117_: *mut crate::leanh::LeanObject,
    mut v_k_5118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5119_ = l_Lean_Json_getObjValD(v_j_5117_, v_k_5118_);
    v___x_5120_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(v___x_5119_);
    return v___x_5120_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7___boxed(
    mut v_j_5121_: *mut crate::leanh::LeanObject,
    mut v_k_5122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5123_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_j_5121_, v_k_5122_);
    crate::leanh::lean_dec_ref(v_k_5122_);
    return v_res_5123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(
    mut v_sz_5124_: usize,
    mut v_i_5125_: usize,
    mut v_bs_5126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5134_: u8 = 0;
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5138_: u8 = 0;
    let mut v_a_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: usize = 0;
    let mut v___x_5143_: usize = 0;
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5127_ = lean_usize_dec_lt(v_i_5125_, v_sz_5124_);
                if v___x_5127_ == 0 {
                    v___x_5128_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5128_, 0, v_bs_5126_);
                    return v___x_5128_;
                } else {
                    v_v_5129_ = lean_array_uget_borrowed(v_bs_5126_, v_i_5125_);
                    crate::leanh::lean_inc(v_v_5129_);
                    v___x_5130_ =
                        l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_v_5129_);
                    if crate::leanh::lean_obj_tag(v___x_5130_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_5126_);
                        v_a_5131_ = crate::leanh::lean_ctor_get(v___x_5130_, 0);
                        v_isSharedCheck_5138_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5130_)) as u8;
                        if v_isSharedCheck_5138_ == 0 {
                            v___x_5133_ = v___x_5130_;
                            v_isShared_5134_ = v_isSharedCheck_5138_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5131_);
                            crate::leanh::lean_dec(v___x_5130_);
                            v___x_5133_ = crate::leanh::lean_box(0);
                            v_isShared_5134_ = v_isSharedCheck_5138_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5139_ = crate::leanh::lean_ctor_get(v___x_5130_, 0);
                        crate::leanh::lean_inc(v_a_5139_);
                        crate::leanh::lean_dec_ref_known(v___x_5130_, 1);
                        v___x_5140_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5141_ = lean_array_uset(v_bs_5126_, v_i_5125_, v___x_5140_);
                        v___x_5142_ = 1usize;
                        v___x_5143_ = lean_usize_add(v_i_5125_, v___x_5142_);
                        v___x_5144_ = lean_array_uset(v_bs_x27_5141_, v_i_5125_, v_a_5139_);
                        v_i_5125_ = v___x_5143_;
                        v_bs_5126_ = v___x_5144_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5134_ == 0 {
                    v___x_5136_ = v___x_5133_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_a_5131_);
                    v___x_5136_ = v_reuseFailAlloc_5137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29___boxed(
    mut v_sz_5146_: *mut crate::leanh::LeanObject,
    mut v_i_5147_: *mut crate::leanh::LeanObject,
    mut v_bs_5148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5149_: usize = 0;
    let mut v_i_boxed_5150_: usize = 0;
    let mut v_res_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5149_ = crate::leanh::lean_unbox_usize(v_sz_5146_);
    crate::leanh::lean_dec(v_sz_5146_);
    v_i_boxed_5150_ = crate::leanh::lean_unbox_usize(v_i_5147_);
    crate::leanh::lean_dec(v_i_5147_);
    v_res_5151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_boxed_5149_, v_i_boxed_5150_, v_bs_5148_);
    return v_res_5151_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(
    mut v_x_5152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5152_) == 4 {
        let mut v_elems_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5154_: usize = 0;
        let mut v___x_5155_: usize = 0;
        let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_5153_ = crate::leanh::lean_ctor_get(v_x_5152_, 0);
        crate::leanh::lean_inc_ref(v_elems_5153_);
        crate::leanh::lean_dec_ref_known(v_x_5152_, 1);
        v_sz_5154_ = lean_array_size(v_elems_5153_);
        v___x_5155_ = 0usize;
        v___x_5156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_5154_, v___x_5155_, v_elems_5153_);
        return v___x_5156_;
    } else {
        let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5157_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0;
        v___x_5158_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_5159_ = l_Lean_Json_pretty(v_x_5152_, v___x_5158_);
        v___x_5160_ = lean_string_append(v___x_5157_, v___x_5159_);
        crate::leanh::lean_dec_ref(v___x_5159_);
        v___x_5161_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
        v___x_5162_ = lean_string_append(v___x_5160_, v___x_5161_);
        v___x_5163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5163_, 0, v___x_5162_);
        return v___x_5163_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(
    mut v_x_5166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5172_: u8 = 0;
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut v_a_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5166_) == 0 {
                    v___x_5167_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0;
                    return v___x_5167_;
                } else {
                    v___x_5168_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(v_x_5166_);
                    if crate::leanh::lean_obj_tag(v___x_5168_) == 0 {
                        v_a_5169_ = crate::leanh::lean_ctor_get(v___x_5168_, 0);
                        v_isSharedCheck_5176_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5168_)) as u8;
                        if v_isSharedCheck_5176_ == 0 {
                            v___x_5171_ = v___x_5168_;
                            v_isShared_5172_ = v_isSharedCheck_5176_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5169_);
                            crate::leanh::lean_dec(v___x_5168_);
                            v___x_5171_ = crate::leanh::lean_box(0);
                            v_isShared_5172_ = v_isSharedCheck_5176_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5177_ = crate::leanh::lean_ctor_get(v___x_5168_, 0);
                        v_isSharedCheck_5185_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5168_)) as u8;
                        if v_isSharedCheck_5185_ == 0 {
                            v___x_5179_ = v___x_5168_;
                            v_isShared_5180_ = v_isSharedCheck_5185_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5177_);
                            crate::leanh::lean_dec(v___x_5168_);
                            v___x_5179_ = crate::leanh::lean_box(0);
                            v_isShared_5180_ = v_isSharedCheck_5185_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5172_ == 0 {
                    v___x_5174_ = v___x_5171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
                    v___x_5174_ = v_reuseFailAlloc_5175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5174_;
            }
            3 => {
                v___x_5181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5181_, 0, v_a_5177_);
                if v_isShared_5180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5179_, 0, v___x_5181_);
                    v___x_5183_ = v___x_5179_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
                    v___x_5183_ = v_reuseFailAlloc_5184_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(
    mut v_j_5186_: *mut crate::leanh::LeanObject,
    mut v_k_5187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5188_ = l_Lean_Json_getObjValD(v_j_5186_, v_k_5187_);
    v___x_5189_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(v___x_5188_);
    return v___x_5189_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13___boxed(
    mut v_j_5190_: *mut crate::leanh::LeanObject,
    mut v_k_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5192_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_j_5190_, v_k_5191_);
    crate::leanh::lean_dec_ref(v_k_5191_);
    return v_res_5192_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(
    mut v_x_5195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut v_a_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5209_: u8 = 0;
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5195_) == 0 {
                    v___x_5196_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0;
                    return v___x_5196_;
                } else {
                    v___x_5197_ = l_Lean_Json_getStr_x3f(v_x_5195_);
                    if crate::leanh::lean_obj_tag(v___x_5197_) == 0 {
                        v_a_5198_ = crate::leanh::lean_ctor_get(v___x_5197_, 0);
                        v_isSharedCheck_5205_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5197_)) as u8;
                        if v_isSharedCheck_5205_ == 0 {
                            v___x_5200_ = v___x_5197_;
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5198_);
                            crate::leanh::lean_dec(v___x_5197_);
                            v___x_5200_ = crate::leanh::lean_box(0);
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5206_ = crate::leanh::lean_ctor_get(v___x_5197_, 0);
                        v_isSharedCheck_5214_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5197_)) as u8;
                        if v_isSharedCheck_5214_ == 0 {
                            v___x_5208_ = v___x_5197_;
                            v_isShared_5209_ = v_isSharedCheck_5214_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5206_);
                            crate::leanh::lean_dec(v___x_5197_);
                            v___x_5208_ = crate::leanh::lean_box(0);
                            v_isShared_5209_ = v_isSharedCheck_5214_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5201_ == 0 {
                    v___x_5203_ = v___x_5200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
                    v___x_5203_ = v_reuseFailAlloc_5204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5203_;
            }
            3 => {
                v___x_5210_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5210_, 0, v_a_5206_);
                if v_isShared_5209_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5208_, 0, v___x_5210_);
                    v___x_5212_ = v___x_5208_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5210_);
                    v___x_5212_ = v_reuseFailAlloc_5213_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(
    mut v_j_5215_: *mut crate::leanh::LeanObject,
    mut v_k_5216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5217_ = l_Lean_Json_getObjValD(v_j_5215_, v_k_5216_);
    v___x_5218_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(v___x_5217_);
    return v___x_5218_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10___boxed(
    mut v_j_5219_: *mut crate::leanh::LeanObject,
    mut v_k_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5221_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_j_5219_, v_k_5220_);
    crate::leanh::lean_dec_ref(v_k_5220_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(
    mut v_json_5222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5228_: u8 = 0;
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5234_: u8 = 0;
    let mut v_a_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5242_: u8 = 0;
    let mut v_a_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v_a_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5259_: u8 = 0;
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5263_: u8 = 0;
    let mut v_a_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5270_: u8 = 0;
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5276_: u8 = 0;
    let mut v_a_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5280_: u8 = 0;
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut v_a_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5291_: u8 = 0;
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5297_: u8 = 0;
    let mut v_a_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut v_a_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5318_: u8 = 0;
    let mut v_a_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5326_: u8 = 0;
    let mut v_a_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5339_: u8 = 0;
    let mut v_a_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5343_: u8 = 0;
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v_a_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut v_a_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5368_: u8 = 0;
    let mut v_a_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5375_: u8 = 0;
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5381_: u8 = 0;
    let mut v_a_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5385_: u8 = 0;
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5389_: u8 = 0;
    let mut v_a_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5402_: u8 = 0;
    let mut v_a_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5406_: u8 = 0;
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5410_: u8 = 0;
    let mut v_a_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5417_: u8 = 0;
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5423_: u8 = 0;
    let mut v_a_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5427_: u8 = 0;
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5431_: u8 = 0;
    let mut v_a_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5438_: u8 = 0;
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5223_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7;
                crate::leanh::lean_inc(v_json_5222_);
                v___x_5224_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_json_5222_, v___x_5223_);
                if crate::leanh::lean_obj_tag(v___x_5224_) == 0 {
                    crate::leanh::lean_dec(v_json_5222_);
                    v_a_5225_ = crate::leanh::lean_ctor_get(v___x_5224_, 0);
                    v_isSharedCheck_5234_ = (!crate::leanh::lean_is_exclusive(v___x_5224_)) as u8;
                    if v_isSharedCheck_5234_ == 0 {
                        v___x_5227_ = v___x_5224_;
                        v_isShared_5228_ = v_isSharedCheck_5234_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5225_);
                        crate::leanh::lean_dec(v___x_5224_);
                        v___x_5227_ = crate::leanh::lean_box(0);
                        v_isShared_5228_ = v_isSharedCheck_5234_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_5224_) == 0 {
                        crate::leanh::lean_dec(v_json_5222_);
                        v_a_5235_ = crate::leanh::lean_ctor_get(v___x_5224_, 0);
                        v_isSharedCheck_5242_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5224_)) as u8;
                        if v_isSharedCheck_5242_ == 0 {
                            v___x_5237_ = v___x_5224_;
                            v_isShared_5238_ = v_isSharedCheck_5242_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5235_);
                            crate::leanh::lean_dec(v___x_5224_);
                            v___x_5237_ = crate::leanh::lean_box(0);
                            v_isShared_5238_ = v_isSharedCheck_5242_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5243_ = crate::leanh::lean_ctor_get(v___x_5224_, 0);
                        crate::leanh::lean_inc(v_a_5243_);
                        crate::leanh::lean_dec_ref_known(v___x_5224_, 1);
                        v___x_5244_ =
                            l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8;
                        crate::leanh::lean_inc(v_json_5222_);
                        v___x_5245_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_json_5222_, v___x_5244_);
                        if crate::leanh::lean_obj_tag(v___x_5245_) == 0 {
                            crate::leanh::lean_dec(v_a_5243_);
                            crate::leanh::lean_dec(v_json_5222_);
                            v_a_5246_ = crate::leanh::lean_ctor_get(v___x_5245_, 0);
                            v_isSharedCheck_5255_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5245_)) as u8;
                            if v_isSharedCheck_5255_ == 0 {
                                v___x_5248_ = v___x_5245_;
                                v_isShared_5249_ = v_isSharedCheck_5255_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5246_);
                                crate::leanh::lean_dec(v___x_5245_);
                                v___x_5248_ = crate::leanh::lean_box(0);
                                v_isShared_5249_ = v_isSharedCheck_5255_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_5245_) == 0 {
                                crate::leanh::lean_dec(v_a_5243_);
                                crate::leanh::lean_dec(v_json_5222_);
                                v_a_5256_ = crate::leanh::lean_ctor_get(v___x_5245_, 0);
                                v_isSharedCheck_5263_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5245_)) as u8;
                                if v_isSharedCheck_5263_ == 0 {
                                    v___x_5258_ = v___x_5245_;
                                    v_isShared_5259_ = v_isSharedCheck_5263_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5256_);
                                    crate::leanh::lean_dec(v___x_5245_);
                                    v___x_5258_ = crate::leanh::lean_box(0);
                                    v_isShared_5259_ = v_isSharedCheck_5263_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5264_ = crate::leanh::lean_ctor_get(v___x_5245_, 0);
                                crate::leanh::lean_inc(v_a_5264_);
                                crate::leanh::lean_dec_ref_known(v___x_5245_, 1);
                                v___x_5265_ =
                                    l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9;
                                crate::leanh::lean_inc(v_json_5222_);
                                v___x_5266_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_json_5222_, v___x_5265_);
                                if crate::leanh::lean_obj_tag(v___x_5266_) == 0 {
                                    crate::leanh::lean_dec(v_a_5264_);
                                    crate::leanh::lean_dec(v_a_5243_);
                                    crate::leanh::lean_dec(v_json_5222_);
                                    v_a_5267_ = crate::leanh::lean_ctor_get(v___x_5266_, 0);
                                    v_isSharedCheck_5276_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5266_)) as u8;
                                    if v_isSharedCheck_5276_ == 0 {
                                        v___x_5269_ = v___x_5266_;
                                        v_isShared_5270_ = v_isSharedCheck_5276_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5267_);
                                        crate::leanh::lean_dec(v___x_5266_);
                                        v___x_5269_ = crate::leanh::lean_box(0);
                                        v_isShared_5270_ = v_isSharedCheck_5276_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_5266_) == 0 {
                                        crate::leanh::lean_dec(v_a_5264_);
                                        crate::leanh::lean_dec(v_a_5243_);
                                        crate::leanh::lean_dec(v_json_5222_);
                                        v_a_5277_ = crate::leanh::lean_ctor_get(v___x_5266_, 0);
                                        v_isSharedCheck_5284_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5266_)) as u8;
                                        if v_isSharedCheck_5284_ == 0 {
                                            v___x_5279_ = v___x_5266_;
                                            v_isShared_5280_ = v_isSharedCheck_5284_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5277_);
                                            crate::leanh::lean_dec(v___x_5266_);
                                            v___x_5279_ = crate::leanh::lean_box(0);
                                            v_isShared_5280_ = v_isSharedCheck_5284_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5285_ = crate::leanh::lean_ctor_get(v___x_5266_, 0);
                                        crate::leanh::lean_inc(v_a_5285_);
                                        crate::leanh::lean_dec_ref_known(v___x_5266_, 1);
                                        v___x_5286_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10;
                                        crate::leanh::lean_inc(v_json_5222_);
                                        v___x_5287_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_5222_, v___x_5286_);
                                        if crate::leanh::lean_obj_tag(v___x_5287_) == 0 {
                                            crate::leanh::lean_dec(v_a_5285_);
                                            crate::leanh::lean_dec(v_a_5264_);
                                            crate::leanh::lean_dec(v_a_5243_);
                                            crate::leanh::lean_dec(v_json_5222_);
                                            v_a_5288_ = crate::leanh::lean_ctor_get(v___x_5287_, 0);
                                            v_isSharedCheck_5297_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5287_))
                                                    as u8;
                                            if v_isSharedCheck_5297_ == 0 {
                                                v___x_5290_ = v___x_5287_;
                                                v_isShared_5291_ = v_isSharedCheck_5297_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5288_);
                                                crate::leanh::lean_dec(v___x_5287_);
                                                v___x_5290_ = crate::leanh::lean_box(0);
                                                v_isShared_5291_ = v_isSharedCheck_5297_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_5287_) == 0 {
                                                crate::leanh::lean_dec(v_a_5285_);
                                                crate::leanh::lean_dec(v_a_5264_);
                                                crate::leanh::lean_dec(v_a_5243_);
                                                crate::leanh::lean_dec(v_json_5222_);
                                                v_a_5298_ =
                                                    crate::leanh::lean_ctor_get(v___x_5287_, 0);
                                                v_isSharedCheck_5305_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5287_))
                                                        as u8;
                                                if v_isSharedCheck_5305_ == 0 {
                                                    v___x_5300_ = v___x_5287_;
                                                    v_isShared_5301_ = v_isSharedCheck_5305_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5298_);
                                                    crate::leanh::lean_dec(v___x_5287_);
                                                    v___x_5300_ = crate::leanh::lean_box(0);
                                                    v_isShared_5301_ = v_isSharedCheck_5305_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5306_ =
                                                    crate::leanh::lean_ctor_get(v___x_5287_, 0);
                                                crate::leanh::lean_inc(v_a_5306_);
                                                crate::leanh::lean_dec_ref_known(v___x_5287_, 1);
                                                v___x_5307_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11;
                                                crate::leanh::lean_inc(v_json_5222_);
                                                v___x_5308_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_json_5222_, v___x_5307_);
                                                if crate::leanh::lean_obj_tag(v___x_5308_) == 0 {
                                                    crate::leanh::lean_dec(v_a_5306_);
                                                    crate::leanh::lean_dec(v_a_5285_);
                                                    crate::leanh::lean_dec(v_a_5264_);
                                                    crate::leanh::lean_dec(v_a_5243_);
                                                    crate::leanh::lean_dec(v_json_5222_);
                                                    v_a_5309_ =
                                                        crate::leanh::lean_ctor_get(v___x_5308_, 0);
                                                    v_isSharedCheck_5318_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5308_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5318_ == 0 {
                                                        v___x_5311_ = v___x_5308_;
                                                        v_isShared_5312_ = v_isSharedCheck_5318_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5309_);
                                                        crate::leanh::lean_dec(v___x_5308_);
                                                        v___x_5311_ = crate::leanh::lean_box(0);
                                                        v_isShared_5312_ = v_isSharedCheck_5318_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if crate::leanh::lean_obj_tag(v___x_5308_) == 0
                                                    {
                                                        crate::leanh::lean_dec(v_a_5306_);
                                                        crate::leanh::lean_dec(v_a_5285_);
                                                        crate::leanh::lean_dec(v_a_5264_);
                                                        crate::leanh::lean_dec(v_a_5243_);
                                                        crate::leanh::lean_dec(v_json_5222_);
                                                        v_a_5319_ = crate::leanh::lean_ctor_get(
                                                            v___x_5308_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_5326_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_5308_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_5326_ == 0 {
                                                            v___x_5321_ = v___x_5308_;
                                                            v_isShared_5322_ =
                                                                v_isSharedCheck_5326_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_5319_);
                                                            crate::leanh::lean_dec(v___x_5308_);
                                                            v___x_5321_ = crate::leanh::lean_box(0);
                                                            v_isShared_5322_ =
                                                                v_isSharedCheck_5326_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_5327_ = crate::leanh::lean_ctor_get(
                                                            v___x_5308_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_5327_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_5308_,
                                                            1,
                                                        );
                                                        v___x_5328_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12;
                                                        crate::leanh::lean_inc(v_json_5222_);
                                                        v___x_5329_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_json_5222_, v___x_5328_);
                                                        if crate::leanh::lean_obj_tag(v___x_5329_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec(v_a_5327_);
                                                            crate::leanh::lean_dec(v_a_5306_);
                                                            crate::leanh::lean_dec(v_a_5285_);
                                                            crate::leanh::lean_dec(v_a_5264_);
                                                            crate::leanh::lean_dec(v_a_5243_);
                                                            crate::leanh::lean_dec(v_json_5222_);
                                                            v_a_5330_ = crate::leanh::lean_ctor_get(
                                                                v___x_5329_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5339_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_5329_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5339_ == 0 {
                                                                v___x_5332_ = v___x_5329_;
                                                                v_isShared_5333_ =
                                                                    v_isSharedCheck_5339_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_5330_);
                                                                crate::leanh::lean_dec(v___x_5329_);
                                                                v___x_5332_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_5333_ =
                                                                    v_isSharedCheck_5339_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_5329_,
                                                            ) == 0
                                                            {
                                                                crate::leanh::lean_dec(v_a_5327_);
                                                                crate::leanh::lean_dec(v_a_5306_);
                                                                crate::leanh::lean_dec(v_a_5285_);
                                                                crate::leanh::lean_dec(v_a_5264_);
                                                                crate::leanh::lean_dec(v_a_5243_);
                                                                crate::leanh::lean_dec(
                                                                    v_json_5222_,
                                                                );
                                                                v_a_5340_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_5329_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_5347_ = (!crate::leanh::lean_is_exclusive(v___x_5329_)) as u8;
                                                                if v_isSharedCheck_5347_ == 0 {
                                                                    v___x_5342_ = v___x_5329_;
                                                                    v_isShared_5343_ =
                                                                        v_isSharedCheck_5347_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_5340_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_5329_,
                                                                    );
                                                                    v___x_5342_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_5343_ =
                                                                        v_isSharedCheck_5347_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_5348_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_5329_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_5348_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_5329_,
                                                                    1,
                                                                );
                                                                v___x_5349_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
                                                                crate::leanh::lean_inc(
                                                                    v_json_5222_,
                                                                );
                                                                v___x_5350_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_5222_, v___x_5349_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_5350_,
                                                                ) == 0
                                                                {
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5348_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5327_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5306_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5285_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5264_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_5243_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_json_5222_,
                                                                    );
                                                                    v_a_5351_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_5350_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_5360_ = (!crate::leanh::lean_is_exclusive(v___x_5350_)) as u8;
                                                                    if v_isSharedCheck_5360_ == 0 {
                                                                        v___x_5353_ = v___x_5350_;
                                                                        v_isShared_5354_ =
                                                                            v_isSharedCheck_5360_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_5351_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_5350_,
                                                                        );
                                                                        v___x_5353_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_5354_ =
                                                                            v_isSharedCheck_5360_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_5350_,
                                                                    ) == 0
                                                                    {
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5348_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5327_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5306_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5285_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5264_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_a_5243_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_json_5222_,
                                                                        );
                                                                        v_a_5361_ = crate::leanh::lean_ctor_get(v___x_5350_, 0);
                                                                        v_isSharedCheck_5368_ = (!crate::leanh::lean_is_exclusive(v___x_5350_)) as u8;
                                                                        if v_isSharedCheck_5368_
                                                                            == 0
                                                                        {
                                                                            v___x_5363_ =
                                                                                v___x_5350_;
                                                                            v_isShared_5364_ = v_isSharedCheck_5368_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_5361_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_5350_,
                                                                            );
                                                                            v___x_5363_ = crate::leanh::lean_box(0);
                                                                            v_isShared_5364_ = v_isSharedCheck_5368_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_5369_ = crate::leanh::lean_ctor_get(v___x_5350_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_5369_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_5350_, 1);
                                                                        v___x_5370_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13;
                                                                        crate::leanh::lean_inc(
                                                                            v_json_5222_,
                                                                        );
                                                                        v___x_5371_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_json_5222_, v___x_5370_);
                                                                        if crate::leanh::lean_obj_tag(v___x_5371_) == 0 {
crate::leanh::lean_dec(v_a_5369_);
crate::leanh::lean_dec(v_a_5348_);
crate::leanh::lean_dec(v_a_5327_);
crate::leanh::lean_dec(v_a_5306_);
crate::leanh::lean_dec(v_a_5285_);
crate::leanh::lean_dec(v_a_5264_);
crate::leanh::lean_dec(v_a_5243_);
crate::leanh::lean_dec(v_json_5222_);
v_a_5372_ = crate::leanh::lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5381_ = (!crate::leanh::lean_is_exclusive(v___x_5371_)) as u8;
if v_isSharedCheck_5381_ == 0 {
v___x_5374_ = v___x_5371_;
v_isShared_5375_ = v_isSharedCheck_5381_;
state = 29; continue;
} else {
crate::leanh::lean_inc(v_a_5372_);
crate::leanh::lean_dec(v___x_5371_);
v___x_5374_ = crate::leanh::lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5381_;
state = 29; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5371_) == 0 {
crate::leanh::lean_dec(v_a_5369_);
crate::leanh::lean_dec(v_a_5348_);
crate::leanh::lean_dec(v_a_5327_);
crate::leanh::lean_dec(v_a_5306_);
crate::leanh::lean_dec(v_a_5285_);
crate::leanh::lean_dec(v_a_5264_);
crate::leanh::lean_dec(v_a_5243_);
crate::leanh::lean_dec(v_json_5222_);
v_a_5382_ = crate::leanh::lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5389_ = (!crate::leanh::lean_is_exclusive(v___x_5371_)) as u8;
if v_isSharedCheck_5389_ == 0 {
v___x_5384_ = v___x_5371_;
v_isShared_5385_ = v_isSharedCheck_5389_;
state = 31; continue;
} else {
crate::leanh::lean_inc(v_a_5382_);
crate::leanh::lean_dec(v___x_5371_);
v___x_5384_ = crate::leanh::lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
state = 31; continue;
}
} else {
v_a_5390_ = crate::leanh::lean_ctor_get(v___x_5371_, 0);
crate::leanh::lean_inc(v_a_5390_);
crate::leanh::lean_dec_ref_known(v___x_5371_, 1);
v___x_5391_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14;
crate::leanh::lean_inc(v_json_5222_);
v___x_5392_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_json_5222_, v___x_5391_);
if crate::leanh::lean_obj_tag(v___x_5392_) == 0 {
crate::leanh::lean_dec(v_a_5390_);
crate::leanh::lean_dec(v_a_5369_);
crate::leanh::lean_dec(v_a_5348_);
crate::leanh::lean_dec(v_a_5327_);
crate::leanh::lean_dec(v_a_5306_);
crate::leanh::lean_dec(v_a_5285_);
crate::leanh::lean_dec(v_a_5264_);
crate::leanh::lean_dec(v_a_5243_);
crate::leanh::lean_dec(v_json_5222_);
v_a_5393_ = crate::leanh::lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5402_ = (!crate::leanh::lean_is_exclusive(v___x_5392_)) as u8;
if v_isSharedCheck_5402_ == 0 {
v___x_5395_ = v___x_5392_;
v_isShared_5396_ = v_isSharedCheck_5402_;
state = 33; continue;
} else {
crate::leanh::lean_inc(v_a_5393_);
crate::leanh::lean_dec(v___x_5392_);
v___x_5395_ = crate::leanh::lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5402_;
state = 33; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5392_) == 0 {
crate::leanh::lean_dec(v_a_5390_);
crate::leanh::lean_dec(v_a_5369_);
crate::leanh::lean_dec(v_a_5348_);
crate::leanh::lean_dec(v_a_5327_);
crate::leanh::lean_dec(v_a_5306_);
crate::leanh::lean_dec(v_a_5285_);
crate::leanh::lean_dec(v_a_5264_);
crate::leanh::lean_dec(v_a_5243_);
crate::leanh::lean_dec(v_json_5222_);
v_a_5403_ = crate::leanh::lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5410_ = (!crate::leanh::lean_is_exclusive(v___x_5392_)) as u8;
if v_isSharedCheck_5410_ == 0 {
v___x_5405_ = v___x_5392_;
v_isShared_5406_ = v_isSharedCheck_5410_;
state = 35; continue;
} else {
crate::leanh::lean_inc(v_a_5403_);
crate::leanh::lean_dec(v___x_5392_);
v___x_5405_ = crate::leanh::lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
state = 35; continue;
}
} else {
v_a_5411_ = crate::leanh::lean_ctor_get(v___x_5392_, 0);
crate::leanh::lean_inc(v_a_5411_);
crate::leanh::lean_dec_ref_known(v___x_5392_, 1);
v___x_5412_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15;
crate::leanh::lean_inc(v_json_5222_);
v___x_5413_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_json_5222_, v___x_5412_);
if crate::leanh::lean_obj_tag(v___x_5413_) == 0 {
crate::leanh::lean_dec(v_a_5411_);
crate::leanh::lean_dec(v_a_5390_);
crate::leanh::lean_dec(v_a_5369_);
crate::leanh::lean_dec(v_a_5348_);
crate::leanh::lean_dec(v_a_5327_);
crate::leanh::lean_dec(v_a_5306_);
crate::leanh::lean_dec(v_a_5285_);
crate::leanh::lean_dec(v_a_5264_);
crate::leanh::lean_dec(v_a_5243_);
crate::leanh::lean_dec(v_json_5222_);
v_a_5414_ = crate::leanh::lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5423_ = (!crate::leanh::lean_is_exclusive(v___x_5413_)) as u8;
if v_isSharedCheck_5423_ == 0 {
v___x_5416_ = v___x_5413_;
v_isShared_5417_ = v_isSharedCheck_5423_;
state = 37; continue;
} else {
crate::leanh::lean_inc(v_a_5414_);
crate::leanh::lean_dec(v___x_5413_);
v___x_5416_ = crate::leanh::lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5423_;
state = 37; continue;
}
} else {
if crate::leanh::lean_obj_tag(v___x_5413_) == 0 {
crate::leanh::lean_dec(v_a_5411_);
crate::leanh::lean_dec(v_a_5390_);
crate::leanh::lean_dec(v_a_5369_);
crate::leanh::lean_dec(v_a_5348_);
crate::leanh::lean_dec(v_a_5327_);
crate::leanh::lean_dec(v_a_5306_);
crate::leanh::lean_dec(v_a_5285_);
crate::leanh::lean_dec(v_a_5264_);
crate::leanh::lean_dec(v_a_5243_);
crate::leanh::lean_dec(v_json_5222_);
v_a_5424_ = crate::leanh::lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5431_ = (!crate::leanh::lean_is_exclusive(v___x_5413_)) as u8;
if v_isSharedCheck_5431_ == 0 {
v___x_5426_ = v___x_5413_;
v_isShared_5427_ = v_isSharedCheck_5431_;
state = 39; continue;
} else {
crate::leanh::lean_inc(v_a_5424_);
crate::leanh::lean_dec(v___x_5413_);
v___x_5426_ = crate::leanh::lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
state = 39; continue;
}
} else {
v_a_5432_ = crate::leanh::lean_ctor_get(v___x_5413_, 0);
crate::leanh::lean_inc(v_a_5432_);
crate::leanh::lean_dec_ref_known(v___x_5413_, 1);
v___x_5433_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16;
v___x_5434_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_json_5222_, v___x_5433_);
v_a_5435_ = crate::leanh::lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5443_ = (!crate::leanh::lean_is_exclusive(v___x_5434_)) as u8;
if v_isSharedCheck_5443_ == 0 {
v___x_5437_ = v___x_5434_;
v_isShared_5438_ = v_isSharedCheck_5443_;
state = 41; continue;
} else {
crate::leanh::lean_inc(v_a_5435_);
crate::leanh::lean_dec(v___x_5434_);
v___x_5437_ = crate::leanh::lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5443_;
state = 41; continue;
}
}
}
}
}
}
}
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5229_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9,
                );
                v___x_5230_ = lean_string_append(v___x_5229_, v_a_5225_);
                crate::leanh::lean_dec(v_a_5225_);
                if v_isShared_5228_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5227_, 0, v___x_5230_);
                    v___x_5232_ = v___x_5227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5233_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5230_);
                    v___x_5232_ = v_reuseFailAlloc_5233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5232_;
            }
            3 => {
                if v_isShared_5238_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5237_, 0);
                    v___x_5240_ = v___x_5237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
                    v___x_5240_ = v_reuseFailAlloc_5241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5240_;
            }
            5 => {
                v___x_5250_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14,
                );
                v___x_5251_ = lean_string_append(v___x_5250_, v_a_5246_);
                crate::leanh::lean_dec(v_a_5246_);
                if v_isShared_5249_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5248_, 0, v___x_5251_);
                    v___x_5253_ = v___x_5248_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5251_);
                    v___x_5253_ = v_reuseFailAlloc_5254_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5253_;
            }
            7 => {
                if v_isShared_5259_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5258_, 0);
                    v___x_5261_ = v___x_5258_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
                    v___x_5261_ = v_reuseFailAlloc_5262_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5261_;
            }
            9 => {
                v___x_5271_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20,
                );
                v___x_5272_ = lean_string_append(v___x_5271_, v_a_5267_);
                crate::leanh::lean_dec(v_a_5267_);
                if v_isShared_5270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5269_, 0, v___x_5272_);
                    v___x_5274_ = v___x_5269_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5275_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5272_);
                    v___x_5274_ = v_reuseFailAlloc_5275_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5274_;
            }
            11 => {
                if v_isShared_5280_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5279_, 0);
                    v___x_5282_ = v___x_5279_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
                    v___x_5282_ = v_reuseFailAlloc_5283_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5282_;
            }
            13 => {
                v___x_5292_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27,
                );
                v___x_5293_ = lean_string_append(v___x_5292_, v_a_5288_);
                crate::leanh::lean_dec(v_a_5288_);
                if v_isShared_5291_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5290_, 0, v___x_5293_);
                    v___x_5295_ = v___x_5290_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5296_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5296_, 0, v___x_5293_);
                    v___x_5295_ = v_reuseFailAlloc_5296_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5295_;
            }
            15 => {
                if v_isShared_5301_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5300_, 0);
                    v___x_5303_ = v___x_5300_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
                    v___x_5303_ = v_reuseFailAlloc_5304_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5303_;
            }
            17 => {
                v___x_5313_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33,
                );
                v___x_5314_ = lean_string_append(v___x_5313_, v_a_5309_);
                crate::leanh::lean_dec(v_a_5309_);
                if v_isShared_5312_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5311_, 0, v___x_5314_);
                    v___x_5316_ = v___x_5311_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5317_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5317_, 0, v___x_5314_);
                    v___x_5316_ = v_reuseFailAlloc_5317_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5316_;
            }
            19 => {
                if v_isShared_5322_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5321_, 0);
                    v___x_5324_ = v___x_5321_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
                    v___x_5324_ = v_reuseFailAlloc_5325_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5324_;
            }
            21 => {
                v___x_5334_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40,
                );
                v___x_5335_ = lean_string_append(v___x_5334_, v_a_5330_);
                crate::leanh::lean_dec(v_a_5330_);
                if v_isShared_5333_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5332_, 0, v___x_5335_);
                    v___x_5337_ = v___x_5332_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5338_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5338_, 0, v___x_5335_);
                    v___x_5337_ = v_reuseFailAlloc_5338_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5337_;
            }
            23 => {
                if v_isShared_5343_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5342_, 0);
                    v___x_5345_ = v___x_5342_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
                    v___x_5345_ = v_reuseFailAlloc_5346_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5345_;
            }
            25 => {
                v___x_5355_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42,
                );
                v___x_5356_ = lean_string_append(v___x_5355_, v_a_5351_);
                crate::leanh::lean_dec(v_a_5351_);
                if v_isShared_5354_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5353_, 0, v___x_5356_);
                    v___x_5358_ = v___x_5353_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5356_);
                    v___x_5358_ = v_reuseFailAlloc_5359_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5358_;
            }
            27 => {
                if v_isShared_5364_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5363_, 0);
                    v___x_5366_ = v___x_5363_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5367_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
                    v___x_5366_ = v_reuseFailAlloc_5367_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5366_;
            }
            29 => {
                v___x_5376_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49,
                );
                v___x_5377_ = lean_string_append(v___x_5376_, v_a_5372_);
                crate::leanh::lean_dec(v_a_5372_);
                if v_isShared_5375_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5374_, 0, v___x_5377_);
                    v___x_5379_ = v___x_5374_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5377_);
                    v___x_5379_ = v_reuseFailAlloc_5380_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5379_;
            }
            31 => {
                if v_isShared_5385_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5384_, 0);
                    v___x_5387_ = v___x_5384_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
                    v___x_5387_ = v_reuseFailAlloc_5388_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5387_;
            }
            33 => {
                v___x_5397_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56,
                );
                v___x_5398_ = lean_string_append(v___x_5397_, v_a_5393_);
                crate::leanh::lean_dec(v_a_5393_);
                if v_isShared_5396_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5395_, 0, v___x_5398_);
                    v___x_5400_ = v___x_5395_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
                    v___x_5400_ = v_reuseFailAlloc_5401_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5400_;
            }
            35 => {
                if v_isShared_5406_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5405_, 0);
                    v___x_5408_ = v___x_5405_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
                    v___x_5408_ = v_reuseFailAlloc_5409_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5408_;
            }
            37 => {
                v___x_5418_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63,
                );
                v___x_5419_ = lean_string_append(v___x_5418_, v_a_5414_);
                crate::leanh::lean_dec(v_a_5414_);
                if v_isShared_5417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5416_, 0, v___x_5419_);
                    v___x_5421_ = v___x_5416_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5419_);
                    v___x_5421_ = v_reuseFailAlloc_5422_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5421_;
            }
            39 => {
                if v_isShared_5427_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5426_, 0);
                    v___x_5429_ = v___x_5426_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5430_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
                    v___x_5429_ = v_reuseFailAlloc_5430_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5429_;
            }
            41 => {
                v___x_5439_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5439_, 0, v_a_5243_);
                crate::leanh::lean_ctor_set(v___x_5439_, 1, v_a_5264_);
                crate::leanh::lean_ctor_set(v___x_5439_, 2, v_a_5285_);
                crate::leanh::lean_ctor_set(v___x_5439_, 3, v_a_5306_);
                crate::leanh::lean_ctor_set(v___x_5439_, 4, v_a_5327_);
                crate::leanh::lean_ctor_set(v___x_5439_, 5, v_a_5348_);
                crate::leanh::lean_ctor_set(v___x_5439_, 6, v_a_5369_);
                crate::leanh::lean_ctor_set(v___x_5439_, 7, v_a_5390_);
                crate::leanh::lean_ctor_set(v___x_5439_, 8, v_a_5411_);
                crate::leanh::lean_ctor_set(v___x_5439_, 9, v_a_5432_);
                crate::leanh::lean_ctor_set(v___x_5439_, 10, v_a_5435_);
                if v_isShared_5438_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5437_, 0, v___x_5439_);
                    v___x_5441_ = v___x_5437_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_5442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5442_, 0, v___x_5439_);
                    v___x_5441_ = v_reuseFailAlloc_5442_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_5441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(
    mut v_sz_5444_: usize,
    mut v_i_5445_: usize,
    mut v_bs_5446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5447_: u8 = 0;
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v_a_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: usize = 0;
    let mut v___x_5463_: usize = 0;
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5447_ = lean_usize_dec_lt(v_i_5445_, v_sz_5444_);
                if v___x_5447_ == 0 {
                    v___x_5448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5448_, 0, v_bs_5446_);
                    return v___x_5448_;
                } else {
                    v_v_5449_ = lean_array_uget_borrowed(v_bs_5446_, v_i_5445_);
                    crate::leanh::lean_inc(v_v_5449_);
                    v___x_5450_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(v_v_5449_);
                    if crate::leanh::lean_obj_tag(v___x_5450_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_5446_);
                        v_a_5451_ = crate::leanh::lean_ctor_get(v___x_5450_, 0);
                        v_isSharedCheck_5458_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5450_)) as u8;
                        if v_isSharedCheck_5458_ == 0 {
                            v___x_5453_ = v___x_5450_;
                            v_isShared_5454_ = v_isSharedCheck_5458_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5451_);
                            crate::leanh::lean_dec(v___x_5450_);
                            v___x_5453_ = crate::leanh::lean_box(0);
                            v_isShared_5454_ = v_isSharedCheck_5458_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5459_ = crate::leanh::lean_ctor_get(v___x_5450_, 0);
                        crate::leanh::lean_inc(v_a_5459_);
                        crate::leanh::lean_dec_ref_known(v___x_5450_, 1);
                        v___x_5460_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5461_ = lean_array_uset(v_bs_5446_, v_i_5445_, v___x_5460_);
                        v___x_5462_ = 1usize;
                        v___x_5463_ = lean_usize_add(v_i_5445_, v___x_5462_);
                        v___x_5464_ = lean_array_uset(v_bs_x27_5461_, v_i_5445_, v_a_5459_);
                        v_i_5445_ = v___x_5463_;
                        v_bs_5446_ = v___x_5464_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5454_ == 0 {
                    v___x_5456_ = v___x_5453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_a_5451_);
                    v___x_5456_ = v_reuseFailAlloc_5457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5456_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6___boxed(
    mut v_sz_5466_: *mut crate::leanh::LeanObject,
    mut v_i_5467_: *mut crate::leanh::LeanObject,
    mut v_bs_5468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5469_: usize = 0;
    let mut v_i_boxed_5470_: usize = 0;
    let mut v_res_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5469_ = crate::leanh::lean_unbox_usize(v_sz_5466_);
    crate::leanh::lean_dec(v_sz_5466_);
    v_i_boxed_5470_ = crate::leanh::lean_unbox_usize(v_i_5467_);
    crate::leanh::lean_dec(v_i_5467_);
    v_res_5471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_boxed_5469_, v_i_boxed_5470_, v_bs_5468_);
    return v_res_5471_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(
    mut v_x_5472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5472_) == 4 {
        let mut v_elems_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5474_: usize = 0;
        let mut v___x_5475_: usize = 0;
        let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_5473_ = crate::leanh::lean_ctor_get(v_x_5472_, 0);
        crate::leanh::lean_inc_ref(v_elems_5473_);
        crate::leanh::lean_dec_ref_known(v_x_5472_, 1);
        v_sz_5474_ = lean_array_size(v_elems_5473_);
        v___x_5475_ = 0usize;
        v___x_5476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_5474_, v___x_5475_, v_elems_5473_);
        return v___x_5476_;
    } else {
        let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5477_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0;
        v___x_5478_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_5479_ = l_Lean_Json_pretty(v_x_5472_, v___x_5478_);
        v___x_5480_ = lean_string_append(v___x_5477_, v___x_5479_);
        crate::leanh::lean_dec_ref(v___x_5479_);
        v___x_5481_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
        v___x_5482_ = lean_string_append(v___x_5480_, v___x_5481_);
        v___x_5483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5483_, 0, v___x_5482_);
        return v___x_5483_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(
    mut v_j_5484_: *mut crate::leanh::LeanObject,
    mut v_k_5485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5486_ = l_Lean_Json_getObjValD(v_j_5484_, v_k_5485_);
    v___x_5487_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(v___x_5486_);
    return v___x_5487_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2___boxed(
    mut v_j_5488_: *mut crate::leanh::LeanObject,
    mut v_k_5489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5490_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_j_5488_, v_k_5489_);
    crate::leanh::lean_dec_ref(v_k_5489_);
    return v_res_5490_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5496_: u8 = 0;
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5496_ = 1;
    v___x_5497_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1;
    v___x_5498_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5497_, v___x_5496_);
    return v___x_5498_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5499_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5;
    v___x_5500_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2,
    );
    v___x_5501_ = lean_string_append(v___x_5500_, v___x_5499_);
    return v___x_5501_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5504_: u8 = 0;
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5504_ = 1;
    v___x_5505_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4;
    v___x_5506_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5505_, v___x_5504_);
    return v___x_5506_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5507_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5,
    );
    v___x_5508_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3,
    );
    v___x_5509_ = lean_string_append(v___x_5508_, v___x_5507_);
    return v___x_5509_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5510_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_5511_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6,
    );
    v___x_5512_ = lean_string_append(v___x_5511_, v___x_5510_);
    return v___x_5512_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5516_: u8 = 0;
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5516_ = 1;
    v___x_5517_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9;
    v___x_5518_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5517_, v___x_5516_);
    return v___x_5518_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5519_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10,
    );
    v___x_5520_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3,
    );
    v___x_5521_ = lean_string_append(v___x_5520_, v___x_5519_);
    return v___x_5521_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5522_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_5523_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11,
    );
    v___x_5524_ = lean_string_append(v___x_5523_, v___x_5522_);
    return v___x_5524_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5528_: u8 = 0;
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5528_ = 1;
    v___x_5529_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14;
    v___x_5530_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5529_, v___x_5528_);
    return v___x_5530_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5531_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15,
    );
    v___x_5532_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3,
    );
    v___x_5533_ = lean_string_append(v___x_5532_, v___x_5531_);
    return v___x_5533_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5534_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_5535_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16,
    );
    v___x_5536_ = lean_string_append(v___x_5535_, v___x_5534_);
    return v___x_5536_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5539_: u8 = 0;
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5539_ = 1;
    v___x_5540_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18;
    v___x_5541_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5540_, v___x_5539_);
    return v___x_5541_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5542_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19,
    );
    v___x_5543_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3,
    );
    v___x_5544_ = lean_string_append(v___x_5543_, v___x_5542_);
    return v___x_5544_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5545_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_5546_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20,
    );
    v___x_5547_ = lean_string_append(v___x_5546_, v___x_5545_);
    return v___x_5547_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(
    mut v_json_5548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5554_: u8 = 0;
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5560_: u8 = 0;
    let mut v_a_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5564_: u8 = 0;
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5568_: u8 = 0;
    let mut v_a_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5575_: u8 = 0;
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut v_a_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5585_: u8 = 0;
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_a_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5596_: u8 = 0;
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v_a_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5606_: u8 = 0;
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5610_: u8 = 0;
    let mut v_a_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5623_: u8 = 0;
    let mut v_a_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5627_: u8 = 0;
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5631_: u8 = 0;
    let mut v_a_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5635_: u8 = 0;
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5549_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0;
                crate::leanh::lean_inc(v_json_5548_);
                v___x_5550_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_5548_, v___x_5549_);
                if crate::leanh::lean_obj_tag(v___x_5550_) == 0 {
                    crate::leanh::lean_dec(v_json_5548_);
                    v_a_5551_ = crate::leanh::lean_ctor_get(v___x_5550_, 0);
                    v_isSharedCheck_5560_ = (!crate::leanh::lean_is_exclusive(v___x_5550_)) as u8;
                    if v_isSharedCheck_5560_ == 0 {
                        v___x_5553_ = v___x_5550_;
                        v_isShared_5554_ = v_isSharedCheck_5560_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5551_);
                        crate::leanh::lean_dec(v___x_5550_);
                        v___x_5553_ = crate::leanh::lean_box(0);
                        v_isShared_5554_ = v_isSharedCheck_5560_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_5550_) == 0 {
                        crate::leanh::lean_dec(v_json_5548_);
                        v_a_5561_ = crate::leanh::lean_ctor_get(v___x_5550_, 0);
                        v_isSharedCheck_5568_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5550_)) as u8;
                        if v_isSharedCheck_5568_ == 0 {
                            v___x_5563_ = v___x_5550_;
                            v_isShared_5564_ = v_isSharedCheck_5568_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5561_);
                            crate::leanh::lean_dec(v___x_5550_);
                            v___x_5563_ = crate::leanh::lean_box(0);
                            v_isShared_5564_ = v_isSharedCheck_5568_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5569_ = crate::leanh::lean_ctor_get(v___x_5550_, 0);
                        crate::leanh::lean_inc(v_a_5569_);
                        crate::leanh::lean_dec_ref_known(v___x_5550_, 1);
                        v___x_5570_ =
                            l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1;
                        crate::leanh::lean_inc(v_json_5548_);
                        v___x_5571_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_json_5548_, v___x_5570_);
                        if crate::leanh::lean_obj_tag(v___x_5571_) == 0 {
                            crate::leanh::lean_dec(v_a_5569_);
                            crate::leanh::lean_dec(v_json_5548_);
                            v_a_5572_ = crate::leanh::lean_ctor_get(v___x_5571_, 0);
                            v_isSharedCheck_5581_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5571_)) as u8;
                            if v_isSharedCheck_5581_ == 0 {
                                v___x_5574_ = v___x_5571_;
                                v_isShared_5575_ = v_isSharedCheck_5581_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5572_);
                                crate::leanh::lean_dec(v___x_5571_);
                                v___x_5574_ = crate::leanh::lean_box(0);
                                v_isShared_5575_ = v_isSharedCheck_5581_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_5571_) == 0 {
                                crate::leanh::lean_dec(v_a_5569_);
                                crate::leanh::lean_dec(v_json_5548_);
                                v_a_5582_ = crate::leanh::lean_ctor_get(v___x_5571_, 0);
                                v_isSharedCheck_5589_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5571_)) as u8;
                                if v_isSharedCheck_5589_ == 0 {
                                    v___x_5584_ = v___x_5571_;
                                    v_isShared_5585_ = v_isSharedCheck_5589_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5582_);
                                    crate::leanh::lean_dec(v___x_5571_);
                                    v___x_5584_ = crate::leanh::lean_box(0);
                                    v_isShared_5585_ = v_isSharedCheck_5589_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5590_ = crate::leanh::lean_ctor_get(v___x_5571_, 0);
                                crate::leanh::lean_inc(v_a_5590_);
                                crate::leanh::lean_dec_ref_known(v___x_5571_, 1);
                                v___x_5591_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2;
                                crate::leanh::lean_inc(v_json_5548_);
                                v___x_5592_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_5548_, v___x_5591_);
                                if crate::leanh::lean_obj_tag(v___x_5592_) == 0 {
                                    crate::leanh::lean_dec(v_a_5590_);
                                    crate::leanh::lean_dec(v_a_5569_);
                                    crate::leanh::lean_dec(v_json_5548_);
                                    v_a_5593_ = crate::leanh::lean_ctor_get(v___x_5592_, 0);
                                    v_isSharedCheck_5602_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5592_)) as u8;
                                    if v_isSharedCheck_5602_ == 0 {
                                        v___x_5595_ = v___x_5592_;
                                        v_isShared_5596_ = v_isSharedCheck_5602_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5593_);
                                        crate::leanh::lean_dec(v___x_5592_);
                                        v___x_5595_ = crate::leanh::lean_box(0);
                                        v_isShared_5596_ = v_isSharedCheck_5602_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_5592_) == 0 {
                                        crate::leanh::lean_dec(v_a_5590_);
                                        crate::leanh::lean_dec(v_a_5569_);
                                        crate::leanh::lean_dec(v_json_5548_);
                                        v_a_5603_ = crate::leanh::lean_ctor_get(v___x_5592_, 0);
                                        v_isSharedCheck_5610_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5592_)) as u8;
                                        if v_isSharedCheck_5610_ == 0 {
                                            v___x_5605_ = v___x_5592_;
                                            v_isShared_5606_ = v_isSharedCheck_5610_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5603_);
                                            crate::leanh::lean_dec(v___x_5592_);
                                            v___x_5605_ = crate::leanh::lean_box(0);
                                            v_isShared_5606_ = v_isSharedCheck_5610_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5611_ = crate::leanh::lean_ctor_get(v___x_5592_, 0);
                                        crate::leanh::lean_inc(v_a_5611_);
                                        crate::leanh::lean_dec_ref_known(v___x_5592_, 1);
                                        v___x_5612_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3;
                                        v___x_5613_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_json_5548_, v___x_5612_);
                                        if crate::leanh::lean_obj_tag(v___x_5613_) == 0 {
                                            crate::leanh::lean_dec(v_a_5611_);
                                            crate::leanh::lean_dec(v_a_5590_);
                                            crate::leanh::lean_dec(v_a_5569_);
                                            v_a_5614_ = crate::leanh::lean_ctor_get(v___x_5613_, 0);
                                            v_isSharedCheck_5623_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5613_))
                                                    as u8;
                                            if v_isSharedCheck_5623_ == 0 {
                                                v___x_5616_ = v___x_5613_;
                                                v_isShared_5617_ = v_isSharedCheck_5623_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5614_);
                                                crate::leanh::lean_dec(v___x_5613_);
                                                v___x_5616_ = crate::leanh::lean_box(0);
                                                v_isShared_5617_ = v_isSharedCheck_5623_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_5613_) == 0 {
                                                crate::leanh::lean_dec(v_a_5611_);
                                                crate::leanh::lean_dec(v_a_5590_);
                                                crate::leanh::lean_dec(v_a_5569_);
                                                v_a_5624_ =
                                                    crate::leanh::lean_ctor_get(v___x_5613_, 0);
                                                v_isSharedCheck_5631_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5613_))
                                                        as u8;
                                                if v_isSharedCheck_5631_ == 0 {
                                                    v___x_5626_ = v___x_5613_;
                                                    v_isShared_5627_ = v_isSharedCheck_5631_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5624_);
                                                    crate::leanh::lean_dec(v___x_5613_);
                                                    v___x_5626_ = crate::leanh::lean_box(0);
                                                    v_isShared_5627_ = v_isSharedCheck_5631_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5632_ =
                                                    crate::leanh::lean_ctor_get(v___x_5613_, 0);
                                                v_isSharedCheck_5640_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5613_))
                                                        as u8;
                                                if v_isSharedCheck_5640_ == 0 {
                                                    v___x_5634_ = v___x_5613_;
                                                    v_isShared_5635_ = v_isSharedCheck_5640_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5632_);
                                                    crate::leanh::lean_dec(v___x_5613_);
                                                    v___x_5634_ = crate::leanh::lean_box(0);
                                                    v_isShared_5635_ = v_isSharedCheck_5640_;
                                                    state = 17;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5555_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7,
                );
                v___x_5556_ = lean_string_append(v___x_5555_, v_a_5551_);
                crate::leanh::lean_dec(v_a_5551_);
                if v_isShared_5554_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5553_, 0, v___x_5556_);
                    v___x_5558_ = v___x_5553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5556_);
                    v___x_5558_ = v_reuseFailAlloc_5559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5558_;
            }
            3 => {
                if v_isShared_5564_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5563_, 0);
                    v___x_5566_ = v___x_5563_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
                    v___x_5566_ = v_reuseFailAlloc_5567_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5566_;
            }
            5 => {
                v___x_5576_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12,
                );
                v___x_5577_ = lean_string_append(v___x_5576_, v_a_5572_);
                crate::leanh::lean_dec(v_a_5572_);
                if v_isShared_5575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5574_, 0, v___x_5577_);
                    v___x_5579_ = v___x_5574_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5577_);
                    v___x_5579_ = v_reuseFailAlloc_5580_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5579_;
            }
            7 => {
                if v_isShared_5585_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5584_, 0);
                    v___x_5587_ = v___x_5584_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_a_5582_);
                    v___x_5587_ = v_reuseFailAlloc_5588_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5587_;
            }
            9 => {
                v___x_5597_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17,
                );
                v___x_5598_ = lean_string_append(v___x_5597_, v_a_5593_);
                crate::leanh::lean_dec(v_a_5593_);
                if v_isShared_5596_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5595_, 0, v___x_5598_);
                    v___x_5600_ = v___x_5595_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5598_);
                    v___x_5600_ = v_reuseFailAlloc_5601_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5600_;
            }
            11 => {
                if v_isShared_5606_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5605_, 0);
                    v___x_5608_ = v___x_5605_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
                    v___x_5608_ = v_reuseFailAlloc_5609_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5608_;
            }
            13 => {
                v___x_5618_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21,
                );
                v___x_5619_ = lean_string_append(v___x_5618_, v_a_5614_);
                crate::leanh::lean_dec(v_a_5614_);
                if v_isShared_5617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5616_, 0, v___x_5619_);
                    v___x_5621_ = v___x_5616_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5622_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5619_);
                    v___x_5621_ = v_reuseFailAlloc_5622_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5621_;
            }
            15 => {
                if v_isShared_5627_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5626_, 0);
                    v___x_5629_ = v___x_5626_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
                    v___x_5629_ = v_reuseFailAlloc_5630_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5629_;
            }
            17 => {
                v___x_5636_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5636_, 0, v_a_5569_);
                crate::leanh::lean_ctor_set(v___x_5636_, 1, v_a_5590_);
                crate::leanh::lean_ctor_set(v___x_5636_, 2, v_a_5611_);
                crate::leanh::lean_ctor_set(v___x_5636_, 3, v_a_5632_);
                if v_isShared_5635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5634_, 0, v___x_5636_);
                    v___x_5638_ = v___x_5634_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5639_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5636_);
                    v___x_5638_ = v_reuseFailAlloc_5639_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5638_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Diagnostics(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Lsp_instInhabitedDiagnosticSeverity_default =
        _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity_default();
    l_Lean_Lsp_instInhabitedDiagnosticSeverity = _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity();
    l_Lean_Lsp_instInhabitedDiagnosticCode_default =
        _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticCode_default);
    l_Lean_Lsp_instInhabitedDiagnosticCode = _init_l_Lean_Lsp_instInhabitedDiagnosticCode();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticCode);
    l_Lean_Lsp_instInhabitedDiagnosticTag_default =
        _init_l_Lean_Lsp_instInhabitedDiagnosticTag_default();
    l_Lean_Lsp_instInhabitedDiagnosticTag = _init_l_Lean_Lsp_instInhabitedDiagnosticTag();
    l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default =
        _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default();
    l_Lean_Lsp_instInhabitedLeanDiagnosticTag = _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag();
    l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default =
        _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default,
    );
    l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation =
        _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation();
    crate::leanh::lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Diagnostics(
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
pub unsafe fn initialize_Lean_Data_Lsp_Diagnostics(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Utf16(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Diagnostics(builtin);
}
