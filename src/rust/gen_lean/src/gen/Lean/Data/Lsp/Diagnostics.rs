// Lean compiler output
// Module: Lean.Data.Lsp.Diagnostics
// Imports: Lean.Data.Lsp.Basic Lean.Data.Lsp.Utf16
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_size, lean_array_to_list,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_int_dec_eq, lean_int_dec_lt,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int, lean_string_append,
    lean_string_compare, lean_string_dec_eq, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_instBEq___redArg___lam__0___boxed,
    l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_flatMapTR_go;
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_id___boxed, l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqBool___boxed,
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
pub static mut l_Lean_Lsp_instInhabitedDiagnosticSeverity_default: u8 = 0;
pub static mut l_Lean_Lsp_instInhabitedDiagnosticSeverity: u8 = 0;
pub static l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqDiagnosticSeverity: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdDiagnosticSeverity: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value:
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
        117, 110, 107, 110, 111, 119, 110, 32, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 83,
        101, 118, 101, 114, 105, 116, 121, 32, 39, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value:
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
    m_data: [39, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((3 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDiagnosticSeverity: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDiagnosticSeverity: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_instInhabitedDiagnosticCode_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Lsp_instInhabitedDiagnosticCode: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instBEqDiagnosticCode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqDiagnosticCode: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instOrdDiagnosticCode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdDiagnosticCode: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0_value:
    leanh::LeanStringObject<50> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDiagnosticCode: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instToJsonDiagnosticCode___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticCode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDiagnosticCode: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedDiagnosticTag_default: u8 = 0;
pub static mut l_Lean_Lsp_instInhabitedDiagnosticTag: u8 = 0;
pub static l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instBEqDiagnosticTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqDiagnosticTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instOrdDiagnosticTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdDiagnosticTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value:
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
        117, 110, 107, 110, 111, 119, 110, 32, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 84,
        97, 103, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDiagnosticTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDiagnosticTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default: u8 = 0;
pub static mut l_Lean_Lsp_instInhabitedLeanDiagnosticTag: u8 = 0;
pub static l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqLeanDiagnosticTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdLeanDiagnosticTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_value:
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
static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_value:
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
static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanDiagnosticTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanDiagnosticTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value:
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
static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value:
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
    m_fun: l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqDiagnosticRelatedInformation: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value:
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
    m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_value:
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
static mut l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonDiagnosticRelatedInformation: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value:
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
    m_data: [76, 115, 112, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value:
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
        68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 82, 101, 108, 97, 116, 101, 100, 73, 110,
        102, 111, 114, 109, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value
) as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value
        ) as *mut leanh::LeanObject,
        3503059123801703312 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value:
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
    m_data: [46, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7_value:
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
            l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11490083008225922661 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12_value:
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
            l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value
        ) as *mut leanh::LeanObject,
        982637797389909653 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value:
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
    m_fun: l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instOrdDiagnosticRelatedInformation: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value:
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
    m_fun: l_Lean_Lsp_instBEqRange_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_value:
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
    m_fun: l_Array_instBEq___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value:
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
    m_fun: l_Array_instBEq___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value:
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
    m_fun: l_Array_instBEq___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value:
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
    m_fun: l_Lean_Json_instBEq___private__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonRange_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value:
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
    m_fun: l_Lean_instToJsonBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value:
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
    m_fun: l_Lean_instToJsonString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_toJson as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_toJson as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_toJson as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6_value:
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
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value:
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
    m_data: [114, 97, 110, 103, 101, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9_value:
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
    m_data: [115, 101, 118, 101, 114, 105, 116, 121, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10_value:
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
    m_data: [105, 115, 83, 105, 108, 101, 110, 116, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11_value:
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
    m_data: [99, 111, 100, 101, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12_value:
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
    m_data: [115, 111, 117, 114, 99, 101, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13_value:
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
    m_data: [116, 97, 103, 115, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14_value:
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
    m_data: [108, 101, 97, 110, 84, 97, 103, 115, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16_value:
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
    m_data: [100, 97, 116, 97, 0],
};
static mut l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonRange_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value:
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
        68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 87, 105, 116, 104, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
        2863902399367947479 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        12743603005877258865 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value:
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
    m_data: [102, 117, 108, 108, 82, 97, 110, 103, 101, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value
        ) as *mut leanh::LeanObject,
        18167956084314672844 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value
        ) as *mut leanh::LeanObject,
        2339750138993587592 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value:
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
    m_fun: l_Lean_Json_getBool_x3f___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value
        ) as *mut leanh::LeanObject,
        6916285088056307392 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value:
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
    m_data: [99, 111, 100, 101, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value
        ) as *mut leanh::LeanObject,
        3386430046879539552 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value:
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
    m_fun: l_Lean_Json_getStr_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value
        ) as *mut leanh::LeanObject,
        7764395542335372806 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value:
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
    m_data: [116, 97, 103, 115, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value
        ) as *mut leanh::LeanObject,
        10757207218291958112 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value
        ) as *mut leanh::LeanObject,
        7655102125566572746 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value:
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
        114, 101, 108, 97, 116, 101, 100, 73, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 63,
        0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value
        ) as *mut leanh::LeanObject,
        15798532268063128341 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value:
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
    m_fun: l_Lean_instFromJsonJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value:
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
    m_data: [100, 97, 116, 97, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67_value:
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
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value
        ) as *mut leanh::LeanObject,
        14378392202104151310 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value:
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
static mut l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instInhabitedPublishDiagnosticsParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqPublishDiagnosticsParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value:
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
    m_data: [117, 114, 105, 0],
};
static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value:
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
    m_data: [
        105, 115, 73, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value:
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
    m_data: [100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 0],
};
static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonPublishDiagnosticsParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value
        ) as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value
        ) as *mut leanh::LeanObject,
        18094239079051600156 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value)
            as *mut leanh::LeanObject,
        6053811214292724070 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value:
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
    m_data: [118, 101, 114, 115, 105, 111, 110, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9_value:
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
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value
        ) as *mut leanh::LeanObject,
        5707914067652744443 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value:
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
        105, 115, 73, 110, 99, 114, 101, 109, 101, 110, 116, 97, 108, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value
) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_value:
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
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value
        ) as *mut leanh::LeanObject,
        2214070583702819421 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value)
            as *mut leanh::LeanObject,
        16258271359659748332 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18_value
) as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonPublishDiagnosticsParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorIdx(
    mut v_x_2822_: u8,
) -> *mut leanh::LeanObject {
    match v_x_2822_ {
        0 => {
            let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2823_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2823_;
        }
        1 => {
            let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2824_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2824_;
        }
        2 => {
            let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2825_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2825_;
        }
        _ => {
            let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2826_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2826_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorIdx___boxed(
    mut v_x_2827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2828_: u8 = 0;
    let mut v_res_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2828_ = (leanh::lean_unbox(v_x_2827_) as u8);
    v_res_2829_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_boxed_2828_);
    return v_res_2829_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(
    mut v_x_2830_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_2830_);
    return v___x_2831_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_toCtorIdx___boxed(
    mut v_x_2832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_2833_: u8 = 0;
    let mut v_res_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2833_ = (leanh::lean_unbox(v_x_2832_) as u8);
    v_res_2834_ = l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(v_x_4__boxed_2833_);
    return v_res_2834_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(
    mut v_k_2835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2835_);
    return v_k_2835_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg___boxed(
    mut v_k_2836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2837_ = l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(v_k_2836_);
    leanh::lean_dec(v_k_2836_);
    return v_res_2837_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorElim(
    mut v_motive_2838_: *mut leanh::LeanObject,
    mut v_ctorIdx_2839_: *mut leanh::LeanObject,
    mut v_t_2840_: u8,
    mut v_h_2841_: *mut leanh::LeanObject,
    mut v_k_2842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2842_);
    return v_k_2842_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_ctorElim___boxed(
    mut v_motive_2843_: *mut leanh::LeanObject,
    mut v_ctorIdx_2844_: *mut leanh::LeanObject,
    mut v_t_2845_: *mut leanh::LeanObject,
    mut v_h_2846_: *mut leanh::LeanObject,
    mut v_k_2847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2848_: u8 = 0;
    let mut v_res_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2848_ = (leanh::lean_unbox(v_t_2845_) as u8);
    v_res_2849_ = l_Lean_Lsp_DiagnosticSeverity_ctorElim(
        v_motive_2843_,
        v_ctorIdx_2844_,
        v_t_boxed_2848_,
        v_h_2846_,
        v_k_2847_,
    );
    leanh::lean_dec(v_k_2847_);
    leanh::lean_dec(v_ctorIdx_2844_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(
    mut v_error_2850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_error_2850_);
    return v_error_2850_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg___boxed(
    mut v_error_2851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(v_error_2851_);
    leanh::lean_dec(v_error_2851_);
    return v_res_2852_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_error_elim(
    mut v_motive_2853_: *mut leanh::LeanObject,
    mut v_t_2854_: u8,
    mut v_h_2855_: *mut leanh::LeanObject,
    mut v_error_2856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_error_2856_);
    return v_error_2856_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_error_elim___boxed(
    mut v_motive_2857_: *mut leanh::LeanObject,
    mut v_t_2858_: *mut leanh::LeanObject,
    mut v_h_2859_: *mut leanh::LeanObject,
    mut v_error_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2861_: u8 = 0;
    let mut v_res_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2861_ = (leanh::lean_unbox(v_t_2858_) as u8);
    v_res_2862_ = l_Lean_Lsp_DiagnosticSeverity_error_elim(
        v_motive_2857_,
        v_t_boxed_2861_,
        v_h_2859_,
        v_error_2860_,
    );
    leanh::lean_dec(v_error_2860_);
    return v_res_2862_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(
    mut v_warning_2863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_warning_2863_);
    return v_warning_2863_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg___boxed(
    mut v_warning_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(v_warning_2864_);
    leanh::lean_dec(v_warning_2864_);
    return v_res_2865_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_warning_elim(
    mut v_motive_2866_: *mut leanh::LeanObject,
    mut v_t_2867_: u8,
    mut v_h_2868_: *mut leanh::LeanObject,
    mut v_warning_2869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_warning_2869_);
    return v_warning_2869_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_warning_elim___boxed(
    mut v_motive_2870_: *mut leanh::LeanObject,
    mut v_t_2871_: *mut leanh::LeanObject,
    mut v_h_2872_: *mut leanh::LeanObject,
    mut v_warning_2873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2874_: u8 = 0;
    let mut v_res_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2874_ = (leanh::lean_unbox(v_t_2871_) as u8);
    v_res_2875_ = l_Lean_Lsp_DiagnosticSeverity_warning_elim(
        v_motive_2870_,
        v_t_boxed_2874_,
        v_h_2872_,
        v_warning_2873_,
    );
    leanh::lean_dec(v_warning_2873_);
    return v_res_2875_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(
    mut v_information_2876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_information_2876_);
    return v_information_2876_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg___boxed(
    mut v_information_2877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2878_ = l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(v_information_2877_);
    leanh::lean_dec(v_information_2877_);
    return v_res_2878_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_information_elim(
    mut v_motive_2879_: *mut leanh::LeanObject,
    mut v_t_2880_: u8,
    mut v_h_2881_: *mut leanh::LeanObject,
    mut v_information_2882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_information_2882_);
    return v_information_2882_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_information_elim___boxed(
    mut v_motive_2883_: *mut leanh::LeanObject,
    mut v_t_2884_: *mut leanh::LeanObject,
    mut v_h_2885_: *mut leanh::LeanObject,
    mut v_information_2886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2887_: u8 = 0;
    let mut v_res_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2887_ = (leanh::lean_unbox(v_t_2884_) as u8);
    v_res_2888_ = l_Lean_Lsp_DiagnosticSeverity_information_elim(
        v_motive_2883_,
        v_t_boxed_2887_,
        v_h_2885_,
        v_information_2886_,
    );
    leanh::lean_dec(v_information_2886_);
    return v_res_2888_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(
    mut v_hint_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_hint_2889_);
    return v_hint_2889_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg___boxed(
    mut v_hint_2890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2891_ = l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(v_hint_2890_);
    leanh::lean_dec(v_hint_2890_);
    return v_res_2891_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_hint_elim(
    mut v_motive_2892_: *mut leanh::LeanObject,
    mut v_t_2893_: u8,
    mut v_h_2894_: *mut leanh::LeanObject,
    mut v_hint_2895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_hint_2895_);
    return v_hint_2895_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticSeverity_hint_elim___boxed(
    mut v_motive_2896_: *mut leanh::LeanObject,
    mut v_t_2897_: *mut leanh::LeanObject,
    mut v_h_2898_: *mut leanh::LeanObject,
    mut v_hint_2899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2900_: u8 = 0;
    let mut v_res_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2900_ = (leanh::lean_unbox(v_t_2897_) as u8);
    v_res_2901_ = l_Lean_Lsp_DiagnosticSeverity_hint_elim(
        v_motive_2896_,
        v_t_boxed_2900_,
        v_h_2898_,
        v_hint_2899_,
    );
    leanh::lean_dec(v_hint_2899_);
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
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: u8 = 0;
    v___x_2906_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_2904_);
    v___x_2907_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_y_2905_);
    v___x_2908_ = lean_nat_dec_eq(v___x_2906_, v___x_2907_);
    leanh::lean_dec(v___x_2907_);
    leanh::lean_dec(v___x_2906_);
    return v___x_2908_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed(
    mut v_x_2909_: *mut leanh::LeanObject,
    mut v_y_2910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_2911_: u8 = 0;
    let mut v_y_18__boxed_2912_: u8 = 0;
    let mut v_res_2913_: u8 = 0;
    let mut v_r_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2911_ = (leanh::lean_unbox(v_x_2909_) as u8);
    v_y_18__boxed_2912_ = (leanh::lean_unbox(v_y_2910_) as u8);
    v_res_2913_ =
        l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v_x_17__boxed_2911_, v_y_18__boxed_2912_);
    v_r_2914_ = leanh::lean_box((v_res_2913_) as usize);
    return v_r_2914_;
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticSeverity_ord(mut v_x_2917_: u8, mut v_y_2918_: u8) -> u8 {
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    v___x_2919_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_2917_);
    v___x_2920_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_y_2918_);
    v___x_2921_ = lean_nat_dec_lt(v___x_2919_, v___x_2920_);
    if v___x_2921_ == 0 {
        let mut v___x_2922_: u8 = 0;
        v___x_2922_ = lean_nat_dec_eq(v___x_2919_, v___x_2920_);
        leanh::lean_dec(v___x_2920_);
        leanh::lean_dec(v___x_2919_);
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
        leanh::lean_dec(v___x_2920_);
        leanh::lean_dec(v___x_2919_);
        v___x_2925_ = 0;
        return v___x_2925_;
    }
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed(
    mut v_x_2926_: *mut leanh::LeanObject,
    mut v_y_2927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_30__boxed_2928_: u8 = 0;
    let mut v_y_31__boxed_2929_: u8 = 0;
    let mut v_res_2930_: u8 = 0;
    let mut v_r_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_2928_ = (leanh::lean_unbox(v_x_2926_) as u8);
    v_y_31__boxed_2929_ = (leanh::lean_unbox(v_y_2927_) as u8);
    v_res_2930_ =
        l_Lean_Lsp_instOrdDiagnosticSeverity_ord(v_x_30__boxed_2928_, v_y_31__boxed_2929_);
    v_r_2931_ = leanh::lean_box((v_res_2930_) as usize);
    return v_r_2931_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0(
    mut v_j_2948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: u8 = 0;
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: u8 = 0;
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_j_2948_);
                v___x_2957_ = l_Lean_Json_getNat_x3f(v_j_2948_);
                if leanh::lean_obj_tag(v___x_2957_) == 1 {
                    v_a_2958_ = leanh::lean_ctor_get(v___x_2957_, 0);
                    leanh::lean_inc(v_a_2958_);
                    leanh::lean_dec_ref_known(v___x_2957_, 1);
                    v___x_2959_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2960_ = lean_nat_dec_eq(v_a_2958_, v___x_2959_);
                    if v___x_2960_ == 0 {
                        v___x_2961_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2962_ = lean_nat_dec_eq(v_a_2958_, v___x_2961_);
                        if v___x_2962_ == 0 {
                            v___x_2963_ = leanh::lean_unsigned_to_nat(3);
                            v___x_2964_ = lean_nat_dec_eq(v_a_2958_, v___x_2963_);
                            if v___x_2964_ == 0 {
                                v___x_2965_ = leanh::lean_unsigned_to_nat(4);
                                v___x_2966_ = lean_nat_dec_eq(v_a_2958_, v___x_2965_);
                                leanh::lean_dec(v_a_2958_);
                                if v___x_2966_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_j_2948_);
                                    v___x_2967_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2;
                                    return v___x_2967_;
                                }
                            } else {
                                leanh::lean_dec(v_a_2958_);
                                leanh::lean_dec(v_j_2948_);
                                v___x_2968_ =
                                    l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3;
                                return v___x_2968_;
                            }
                        } else {
                            leanh::lean_dec(v_a_2958_);
                            leanh::lean_dec(v_j_2948_);
                            v___x_2969_ =
                                l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4;
                            return v___x_2969_;
                        }
                    } else {
                        leanh::lean_dec(v_a_2958_);
                        leanh::lean_dec(v_j_2948_);
                        v___x_2970_ =
                            l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5;
                        return v___x_2970_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2957_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2950_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0;
                v___x_2951_ = leanh::lean_unsigned_to_nat(80);
                v___x_2952_ = l_Lean_Json_pretty(v_j_2948_, v___x_2951_);
                v___x_2953_ = lean_string_append(v___x_2950_, v___x_2952_);
                leanh::lean_dec_ref(v___x_2952_);
                v___x_2954_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
                v___x_2955_ = lean_string_append(v___x_2953_, v___x_2954_);
                v___x_2956_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2956_, 0, v___x_2955_);
                return v___x_2956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2973_ = leanh::lean_unsigned_to_nat(1);
    v___x_2974_ = l_Lean_JsonNumber_fromNat(v___x_2973_);
    return v___x_2974_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2975_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0_once),
        _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0,
    );
    v___x_2976_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2976_, 0, v___x_2975_);
    return v___x_2976_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2977_ = leanh::lean_unsigned_to_nat(2);
    v___x_2978_ = l_Lean_JsonNumber_fromNat(v___x_2977_);
    return v___x_2978_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2979_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2_once),
        _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2,
    );
    v___x_2980_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2980_, 0, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2981_ = leanh::lean_unsigned_to_nat(3);
    v___x_2982_ = l_Lean_JsonNumber_fromNat(v___x_2981_);
    return v___x_2982_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2983_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4_once),
        _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4,
    );
    v___x_2984_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2984_, 0, v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2985_ = leanh::lean_unsigned_to_nat(4);
    v___x_2986_ = l_Lean_JsonNumber_fromNat(v___x_2985_);
    return v___x_2986_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2987_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6_once),
        _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6,
    );
    v___x_2988_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2988_, 0, v___x_2987_);
    return v___x_2988_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(
    mut v_x_2989_: u8,
) -> *mut leanh::LeanObject {
    match v_x_2989_ {
        0 => {
            let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2990_ = leanh::lean_obj_once(
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
            let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2991_ = leanh::lean_obj_once(
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
            let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2992_ = leanh::lean_obj_once(
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
            let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2993_ = leanh::lean_obj_once(
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
    mut v_x_2994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_106__boxed_2995_: u8 = 0;
    let mut v_res_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_106__boxed_2995_ = (leanh::lean_unbox(v_x_2994_) as u8);
    v_res_2996_ = l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(v_x_106__boxed_2995_);
    return v_res_2996_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorIdx(
    mut v_x_2999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2999_) == 0 {
        let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3000_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3000_;
    } else {
        let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3001_ = leanh::lean_unsigned_to_nat(1);
        return v___x_3001_;
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorIdx___boxed(
    mut v_x_3002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3003_ = l_Lean_Lsp_DiagnosticCode_ctorIdx(v_x_3002_);
    leanh::lean_dec_ref(v_x_3002_);
    return v_res_3003_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(
    mut v_t_3004_: *mut leanh::LeanObject,
    mut v_k_3005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_3004_) == 0 {
        let mut v_i_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_i_3006_ = leanh::lean_ctor_get(v_t_3004_, 0);
        leanh::lean_inc(v_i_3006_);
        leanh::lean_dec_ref_known(v_t_3004_, 1);
        v___x_3007_ = leanh::lean_apply_1(v_k_3005_, v_i_3006_);
        return v___x_3007_;
    } else {
        let mut v_s_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_s_3008_ = leanh::lean_ctor_get(v_t_3004_, 0);
        leanh::lean_inc_ref(v_s_3008_);
        leanh::lean_dec_ref_known(v_t_3004_, 1);
        v___x_3009_ = leanh::lean_apply_1(v_k_3005_, v_s_3008_);
        return v___x_3009_;
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorElim(
    mut v_motive_3010_: *mut leanh::LeanObject,
    mut v_ctorIdx_3011_: *mut leanh::LeanObject,
    mut v_t_3012_: *mut leanh::LeanObject,
    mut v_h_3013_: *mut leanh::LeanObject,
    mut v_k_3014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3015_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3012_, v_k_3014_);
    return v___x_3015_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_ctorElim___boxed(
    mut v_motive_3016_: *mut leanh::LeanObject,
    mut v_ctorIdx_3017_: *mut leanh::LeanObject,
    mut v_t_3018_: *mut leanh::LeanObject,
    mut v_h_3019_: *mut leanh::LeanObject,
    mut v_k_3020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Lean_Lsp_DiagnosticCode_ctorElim(
        v_motive_3016_,
        v_ctorIdx_3017_,
        v_t_3018_,
        v_h_3019_,
        v_k_3020_,
    );
    leanh::lean_dec(v_ctorIdx_3017_);
    return v_res_3021_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_int_elim___redArg(
    mut v_t_3022_: *mut leanh::LeanObject,
    mut v_int_3023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3024_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3022_, v_int_3023_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_int_elim(
    mut v_motive_3025_: *mut leanh::LeanObject,
    mut v_t_3026_: *mut leanh::LeanObject,
    mut v_h_3027_: *mut leanh::LeanObject,
    mut v_int_3028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3029_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3026_, v_int_3028_);
    return v___x_3029_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_string_elim___redArg(
    mut v_t_3030_: *mut leanh::LeanObject,
    mut v_string_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3030_, v_string_3031_);
    return v___x_3032_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticCode_string_elim(
    mut v_motive_3033_: *mut leanh::LeanObject,
    mut v_t_3034_: *mut leanh::LeanObject,
    mut v_h_3035_: *mut leanh::LeanObject,
    mut v_string_3036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3037_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_3034_, v_string_3036_);
    return v___x_3037_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3038_ = leanh::lean_unsigned_to_nat(0);
    v___x_3039_ = lean_nat_to_int(v___x_3038_);
    return v___x_3039_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3040_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once),
        _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0,
    );
    v___x_3041_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3041_, 0, v___x_3040_);
    return v___x_3041_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default() -> *mut leanh::LeanObject
{
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3042_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once),
        _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1,
    );
    return v___x_3042_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticCode() -> *mut leanh::LeanObject {
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = l_Lean_Lsp_instInhabitedDiagnosticCode_default;
    return v___x_3043_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticCode_beq(
    mut v_x_3044_: *mut leanh::LeanObject,
    mut v_x_3045_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3044_) == 0 {
        if leanh::lean_obj_tag(v_x_3045_) == 0 {
            let mut v_i_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3048_: u8 = 0;
            v_i_3046_ = leanh::lean_ctor_get(v_x_3044_, 0);
            v_i_3047_ = leanh::lean_ctor_get(v_x_3045_, 0);
            v___x_3048_ = lean_int_dec_eq(v_i_3046_, v_i_3047_);
            return v___x_3048_;
        } else {
            let mut v___x_3049_: u8 = 0;
            v___x_3049_ = 0;
            return v___x_3049_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_3045_) == 1 {
            let mut v_s_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3052_: u8 = 0;
            v_s_3050_ = leanh::lean_ctor_get(v_x_3044_, 0);
            v_s_3051_ = leanh::lean_ctor_get(v_x_3045_, 0);
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
    mut v_x_3054_: *mut leanh::LeanObject,
    mut v_x_3055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3056_: u8 = 0;
    let mut v_r_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_x_3054_, v_x_3055_);
    leanh::lean_dec_ref(v_x_3055_);
    leanh::lean_dec_ref(v_x_3054_);
    v_r_3057_ = leanh::lean_box((v_res_3056_) as usize);
    return v_r_3057_;
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticCode_ord(
    mut v_x_3060_: *mut leanh::LeanObject,
    mut v_x_3061_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3060_) == 0 {
        if leanh::lean_obj_tag(v_x_3061_) == 0 {
            let mut v_i_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3064_: u8 = 0;
            v_i_3062_ = leanh::lean_ctor_get(v_x_3060_, 0);
            v_i_3063_ = leanh::lean_ctor_get(v_x_3061_, 0);
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
        if leanh::lean_obj_tag(v_x_3061_) == 0 {
            let mut v___x_3070_: u8 = 0;
            v___x_3070_ = 2;
            return v___x_3070_;
        } else {
            let mut v_s_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_s_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3073_: u8 = 0;
            v_s_3071_ = leanh::lean_ctor_get(v_x_3060_, 0);
            v_s_3072_ = leanh::lean_ctor_get(v_x_3061_, 0);
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
    mut v_x_3074_: *mut leanh::LeanObject,
    mut v_x_3075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3076_: u8 = 0;
    let mut v_r_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3076_ = l_Lean_Lsp_instOrdDiagnosticCode_ord(v_x_3074_, v_x_3075_);
    leanh::lean_dec_ref(v_x_3075_);
    leanh::lean_dec_ref(v_x_3074_);
    v_r_3077_ = leanh::lean_box((v_res_3076_) as usize);
    return v_r_3077_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0(
    mut v_x_3081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut v_unused_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3081_) {
                2 => {
                    v_n_3090_ = leanh::lean_ctor_get(v_x_3081_, 0);
                    v_mantissa_3091_ = leanh::lean_ctor_get(v_n_3090_, 0);
                    v_exponent_3092_ = leanh::lean_ctor_get(v_n_3090_, 1);
                    v___x_3093_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3094_ = lean_nat_dec_eq(v_exponent_3092_, v___x_3093_);
                    if v___x_3094_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_mantissa_3091_);
                        v_isSharedCheck_3102_ = (!leanh::lean_is_exclusive(v_x_3081_)) as u8;
                        if v_isSharedCheck_3102_ == 0 {
                            v_unused_3103_ = leanh::lean_ctor_get(v_x_3081_, 0);
                            leanh::lean_dec(v_unused_3103_);
                            v___x_3096_ = v_x_3081_;
                            v_isShared_3097_ = v_isSharedCheck_3102_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3081_);
                            v___x_3096_ = leanh::lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3102_;
                            state = 2;
                            continue;
                        }
                    }
                }
                3 => {
                    v_s_3104_ = leanh::lean_ctor_get(v_x_3081_, 0);
                    v_isSharedCheck_3112_ = (!leanh::lean_is_exclusive(v_x_3081_)) as u8;
                    if v_isSharedCheck_3112_ == 0 {
                        v___x_3106_ = v_x_3081_;
                        v_isShared_3107_ = v_isSharedCheck_3112_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_3104_);
                        leanh::lean_dec(v_x_3081_);
                        v___x_3106_ = leanh::lean_box(0);
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
                v___x_3084_ = leanh::lean_unsigned_to_nat(80);
                v___x_3085_ = l_Lean_Json_pretty(v_x_3081_, v___x_3084_);
                v___x_3086_ = lean_string_append(v___x_3083_, v___x_3085_);
                leanh::lean_dec_ref(v___x_3085_);
                v___x_3087_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
                v___x_3088_ = lean_string_append(v___x_3086_, v___x_3087_);
                v___x_3089_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3089_, 0, v___x_3088_);
                return v___x_3089_;
            }
            2 => {
                if v_isShared_3097_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3096_, 0);
                    leanh::lean_ctor_set(v___x_3096_, 0, v_mantissa_3091_);
                    v___x_3099_ = v___x_3096_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3101_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_mantissa_3091_);
                    v___x_3099_ = v_reuseFailAlloc_3101_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3100_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3100_, 0, v___x_3099_);
                return v___x_3100_;
            }
            4 => {
                if v_isShared_3107_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3106_, 1);
                    v___x_3109_ = v___x_3106_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_s_3104_);
                    v___x_3109_ = v_reuseFailAlloc_3111_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3110_, 0, v___x_3109_);
                return v___x_3110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticCode___lam__0(
    mut v_x_3115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v_s_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3115_) == 0 {
                    v_i_3116_ = leanh::lean_ctor_get(v_x_3115_, 0);
                    v_isSharedCheck_3124_ = (!leanh::lean_is_exclusive(v_x_3115_)) as u8;
                    if v_isSharedCheck_3124_ == 0 {
                        v___x_3118_ = v_x_3115_;
                        v_isShared_3119_ = v_isSharedCheck_3124_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_3116_);
                        leanh::lean_dec(v_x_3115_);
                        v___x_3118_ = leanh::lean_box(0);
                        v_isShared_3119_ = v_isSharedCheck_3124_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_s_3125_ = leanh::lean_ctor_get(v_x_3115_, 0);
                    v_isSharedCheck_3132_ = (!leanh::lean_is_exclusive(v_x_3115_)) as u8;
                    if v_isSharedCheck_3132_ == 0 {
                        v___x_3127_ = v_x_3115_;
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_s_3125_);
                        leanh::lean_dec(v_x_3115_);
                        v___x_3127_ = leanh::lean_box(0);
                        v_isShared_3128_ = v_isSharedCheck_3132_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3120_ = l_Lean_JsonNumber_fromInt(v_i_3116_);
                if v_isShared_3119_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3118_, 2);
                    leanh::lean_ctor_set(v___x_3118_, 0, v___x_3120_);
                    v___x_3122_ = v___x_3118_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
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
                    leanh::lean_ctor_set_tag(v___x_3127_, 3);
                    v___x_3130_ = v___x_3127_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3131_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_s_3125_);
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
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorIdx(mut v_x_3135_: u8) -> *mut leanh::LeanObject {
    if v_x_3135_ == 0 {
        let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3136_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3136_;
    } else {
        let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3137_ = leanh::lean_unsigned_to_nat(1);
        return v___x_3137_;
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorIdx___boxed(
    mut v_x_3138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_3139_: u8 = 0;
    let mut v_res_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3139_ = (leanh::lean_unbox(v_x_3138_) as u8);
    v_res_3140_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_boxed_3139_);
    return v_res_3140_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_toCtorIdx(
    mut v_x_3141_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3142_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_3141_);
    return v___x_3142_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_toCtorIdx___boxed(
    mut v_x_3143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_3144_: u8 = 0;
    let mut v_res_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3144_ = (leanh::lean_unbox(v_x_3143_) as u8);
    v_res_3145_ = l_Lean_Lsp_DiagnosticTag_toCtorIdx(v_x_4__boxed_3144_);
    return v_res_3145_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(
    mut v_k_3146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_3146_);
    return v_k_3146_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorElim___redArg___boxed(
    mut v_k_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(v_k_3147_);
    leanh::lean_dec(v_k_3147_);
    return v_res_3148_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorElim(
    mut v_motive_3149_: *mut leanh::LeanObject,
    mut v_ctorIdx_3150_: *mut leanh::LeanObject,
    mut v_t_3151_: u8,
    mut v_h_3152_: *mut leanh::LeanObject,
    mut v_k_3153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_3153_);
    return v_k_3153_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_ctorElim___boxed(
    mut v_motive_3154_: *mut leanh::LeanObject,
    mut v_ctorIdx_3155_: *mut leanh::LeanObject,
    mut v_t_3156_: *mut leanh::LeanObject,
    mut v_h_3157_: *mut leanh::LeanObject,
    mut v_k_3158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3159_: u8 = 0;
    let mut v_res_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3159_ = (leanh::lean_unbox(v_t_3156_) as u8);
    v_res_3160_ = l_Lean_Lsp_DiagnosticTag_ctorElim(
        v_motive_3154_,
        v_ctorIdx_3155_,
        v_t_boxed_3159_,
        v_h_3157_,
        v_k_3158_,
    );
    leanh::lean_dec(v_k_3158_);
    leanh::lean_dec(v_ctorIdx_3155_);
    return v_res_3160_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(
    mut v_unnecessary_3161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_unnecessary_3161_);
    return v_unnecessary_3161_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg___boxed(
    mut v_unnecessary_3162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3163_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(v_unnecessary_3162_);
    leanh::lean_dec(v_unnecessary_3162_);
    return v_res_3163_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_unnecessary_elim(
    mut v_motive_3164_: *mut leanh::LeanObject,
    mut v_t_3165_: u8,
    mut v_h_3166_: *mut leanh::LeanObject,
    mut v_unnecessary_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_unnecessary_3167_);
    return v_unnecessary_3167_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_unnecessary_elim___boxed(
    mut v_motive_3168_: *mut leanh::LeanObject,
    mut v_t_3169_: *mut leanh::LeanObject,
    mut v_h_3170_: *mut leanh::LeanObject,
    mut v_unnecessary_3171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3172_: u8 = 0;
    let mut v_res_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3172_ = (leanh::lean_unbox(v_t_3169_) as u8);
    v_res_3173_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim(
        v_motive_3168_,
        v_t_boxed_3172_,
        v_h_3170_,
        v_unnecessary_3171_,
    );
    leanh::lean_dec(v_unnecessary_3171_);
    return v_res_3173_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(
    mut v_deprecated_3174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_deprecated_3174_);
    return v_deprecated_3174_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg___boxed(
    mut v_deprecated_3175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(v_deprecated_3175_);
    leanh::lean_dec(v_deprecated_3175_);
    return v_res_3176_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_deprecated_elim(
    mut v_motive_3177_: *mut leanh::LeanObject,
    mut v_t_3178_: u8,
    mut v_h_3179_: *mut leanh::LeanObject,
    mut v_deprecated_3180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_deprecated_3180_);
    return v_deprecated_3180_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticTag_deprecated_elim___boxed(
    mut v_motive_3181_: *mut leanh::LeanObject,
    mut v_t_3182_: *mut leanh::LeanObject,
    mut v_h_3183_: *mut leanh::LeanObject,
    mut v_deprecated_3184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3185_: u8 = 0;
    let mut v_res_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3185_ = (leanh::lean_unbox(v_t_3182_) as u8);
    v_res_3186_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim(
        v_motive_3181_,
        v_t_boxed_3185_,
        v_h_3183_,
        v_deprecated_3184_,
    );
    leanh::lean_dec(v_deprecated_3184_);
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
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: u8 = 0;
    v___x_3191_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_3189_);
    v___x_3192_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_y_3190_);
    v___x_3193_ = lean_nat_dec_eq(v___x_3191_, v___x_3192_);
    leanh::lean_dec(v___x_3192_);
    leanh::lean_dec(v___x_3191_);
    return v___x_3193_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed(
    mut v_x_3194_: *mut leanh::LeanObject,
    mut v_y_3195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_3196_: u8 = 0;
    let mut v_y_18__boxed_3197_: u8 = 0;
    let mut v_res_3198_: u8 = 0;
    let mut v_r_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_3196_ = (leanh::lean_unbox(v_x_3194_) as u8);
    v_y_18__boxed_3197_ = (leanh::lean_unbox(v_y_3195_) as u8);
    v_res_3198_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v_x_17__boxed_3196_, v_y_18__boxed_3197_);
    v_r_3199_ = leanh::lean_box((v_res_3198_) as usize);
    return v_r_3199_;
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticTag_ord(mut v_x_3202_: u8, mut v_y_3203_: u8) -> u8 {
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    v___x_3204_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_3202_);
    v___x_3205_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_y_3203_);
    v___x_3206_ = lean_nat_dec_lt(v___x_3204_, v___x_3205_);
    if v___x_3206_ == 0 {
        let mut v___x_3207_: u8 = 0;
        v___x_3207_ = lean_nat_dec_eq(v___x_3204_, v___x_3205_);
        leanh::lean_dec(v___x_3205_);
        leanh::lean_dec(v___x_3204_);
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
        leanh::lean_dec(v___x_3205_);
        leanh::lean_dec(v___x_3204_);
        v___x_3210_ = 0;
        return v___x_3210_;
    }
}
pub unsafe fn l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed(
    mut v_x_3211_: *mut leanh::LeanObject,
    mut v_y_3212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_30__boxed_3213_: u8 = 0;
    let mut v_y_31__boxed_3214_: u8 = 0;
    let mut v_res_3215_: u8 = 0;
    let mut v_r_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_3213_ = (leanh::lean_unbox(v_x_3211_) as u8);
    v_y_31__boxed_3214_ = (leanh::lean_unbox(v_y_3212_) as u8);
    v_res_3215_ = l_Lean_Lsp_instOrdDiagnosticTag_ord(v_x_30__boxed_3213_, v_y_31__boxed_3214_);
    v_r_3216_ = leanh::lean_box((v_res_3215_) as usize);
    return v_r_3216_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0(
    mut v_j_3228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u8 = 0;
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3231_ = l_Lean_Json_getNat_x3f(v_j_3228_);
                if leanh::lean_obj_tag(v___x_3231_) == 1 {
                    v_a_3232_ = leanh::lean_ctor_get(v___x_3231_, 0);
                    leanh::lean_inc(v_a_3232_);
                    leanh::lean_dec_ref_known(v___x_3231_, 1);
                    v___x_3233_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3234_ = lean_nat_dec_eq(v_a_3232_, v___x_3233_);
                    if v___x_3234_ == 0 {
                        v___x_3235_ = leanh::lean_unsigned_to_nat(2);
                        v___x_3236_ = lean_nat_dec_eq(v_a_3232_, v___x_3235_);
                        leanh::lean_dec(v_a_3232_);
                        if v___x_3236_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_3237_ = l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2;
                            return v___x_3237_;
                        }
                    } else {
                        leanh::lean_dec(v_a_3232_);
                        v___x_3238_ = l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3;
                        return v___x_3238_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3231_);
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
) -> *mut leanh::LeanObject {
    if v_x_3241_ == 0 {
        let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3242_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once
            ),
            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1,
        );
        return v___x_3242_;
    } else {
        let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3243_ = leanh::lean_obj_once(
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
    mut v_x_3244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_48__boxed_3245_: u8 = 0;
    let mut v_res_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_48__boxed_3245_ = (leanh::lean_unbox(v_x_3244_) as u8);
    v_res_3246_ = l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(v_x_48__boxed_3245_);
    return v_res_3246_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(
    mut v_x_3249_: u8,
) -> *mut leanh::LeanObject {
    if v_x_3249_ == 0 {
        let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3250_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3250_;
    } else {
        let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3251_ = leanh::lean_unsigned_to_nat(1);
        return v___x_3251_;
    }
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___boxed(
    mut v_x_3252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_3253_: u8 = 0;
    let mut v_res_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3253_ = (leanh::lean_unbox(v_x_3252_) as u8);
    v_res_3254_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_boxed_3253_);
    return v_res_3254_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(
    mut v_x_3255_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx___boxed(
    mut v_x_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_3258_: u8 = 0;
    let mut v_res_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3258_ = (leanh::lean_unbox(v_x_3257_) as u8);
    v_res_3259_ = l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(v_x_4__boxed_3258_);
    return v_res_3259_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(
    mut v_k_3260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_3260_);
    return v_k_3260_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg___boxed(
    mut v_k_3261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3262_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(v_k_3261_);
    leanh::lean_dec(v_k_3261_);
    return v_res_3262_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorElim(
    mut v_motive_3263_: *mut leanh::LeanObject,
    mut v_ctorIdx_3264_: *mut leanh::LeanObject,
    mut v_t_3265_: u8,
    mut v_h_3266_: *mut leanh::LeanObject,
    mut v_k_3267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_3267_);
    return v_k_3267_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_ctorElim___boxed(
    mut v_motive_3268_: *mut leanh::LeanObject,
    mut v_ctorIdx_3269_: *mut leanh::LeanObject,
    mut v_t_3270_: *mut leanh::LeanObject,
    mut v_h_3271_: *mut leanh::LeanObject,
    mut v_k_3272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3273_: u8 = 0;
    let mut v_res_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3273_ = (leanh::lean_unbox(v_t_3270_) as u8);
    v_res_3274_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim(
        v_motive_3268_,
        v_ctorIdx_3269_,
        v_t_boxed_3273_,
        v_h_3271_,
        v_k_3272_,
    );
    leanh::lean_dec(v_k_3272_);
    leanh::lean_dec(v_ctorIdx_3269_);
    return v_res_3274_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(
    mut v_unsolvedGoals_3275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_unsolvedGoals_3275_);
    return v_unsolvedGoals_3275_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg___boxed(
    mut v_unsolvedGoals_3276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3277_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(v_unsolvedGoals_3276_);
    leanh::lean_dec(v_unsolvedGoals_3276_);
    return v_res_3277_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(
    mut v_motive_3278_: *mut leanh::LeanObject,
    mut v_t_3279_: u8,
    mut v_h_3280_: *mut leanh::LeanObject,
    mut v_unsolvedGoals_3281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_unsolvedGoals_3281_);
    return v_unsolvedGoals_3281_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___boxed(
    mut v_motive_3282_: *mut leanh::LeanObject,
    mut v_t_3283_: *mut leanh::LeanObject,
    mut v_h_3284_: *mut leanh::LeanObject,
    mut v_unsolvedGoals_3285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3286_: u8 = 0;
    let mut v_res_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3286_ = (leanh::lean_unbox(v_t_3283_) as u8);
    v_res_3287_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(
        v_motive_3282_,
        v_t_boxed_3286_,
        v_h_3284_,
        v_unsolvedGoals_3285_,
    );
    leanh::lean_dec(v_unsolvedGoals_3285_);
    return v_res_3287_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(
    mut v_goalsAccomplished_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_goalsAccomplished_3288_);
    return v_goalsAccomplished_3288_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg___boxed(
    mut v_goalsAccomplished_3289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3290_ =
        l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(v_goalsAccomplished_3289_);
    leanh::lean_dec(v_goalsAccomplished_3289_);
    return v_res_3290_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(
    mut v_motive_3291_: *mut leanh::LeanObject,
    mut v_t_3292_: u8,
    mut v_h_3293_: *mut leanh::LeanObject,
    mut v_goalsAccomplished_3294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_goalsAccomplished_3294_);
    return v_goalsAccomplished_3294_;
}
pub unsafe fn l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___boxed(
    mut v_motive_3295_: *mut leanh::LeanObject,
    mut v_t_3296_: *mut leanh::LeanObject,
    mut v_h_3297_: *mut leanh::LeanObject,
    mut v_goalsAccomplished_3298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3299_: u8 = 0;
    let mut v_res_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3299_ = (leanh::lean_unbox(v_t_3296_) as u8);
    v_res_3300_ = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(
        v_motive_3295_,
        v_t_boxed_3299_,
        v_h_3297_,
        v_goalsAccomplished_3298_,
    );
    leanh::lean_dec(v_goalsAccomplished_3298_);
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
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: u8 = 0;
    v___x_3305_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_3303_);
    v___x_3306_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_y_3304_);
    v___x_3307_ = lean_nat_dec_eq(v___x_3305_, v___x_3306_);
    leanh::lean_dec(v___x_3306_);
    leanh::lean_dec(v___x_3305_);
    return v___x_3307_;
}
pub unsafe fn l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed(
    mut v_x_3308_: *mut leanh::LeanObject,
    mut v_y_3309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_3310_: u8 = 0;
    let mut v_y_18__boxed_3311_: u8 = 0;
    let mut v_res_3312_: u8 = 0;
    let mut v_r_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_3310_ = (leanh::lean_unbox(v_x_3308_) as u8);
    v_y_18__boxed_3311_ = (leanh::lean_unbox(v_y_3309_) as u8);
    v_res_3312_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v_x_17__boxed_3310_, v_y_18__boxed_3311_);
    v_r_3313_ = leanh::lean_box((v_res_3312_) as usize);
    return v_r_3313_;
}
pub unsafe fn l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(mut v_x_3316_: u8, mut v_y_3317_: u8) -> u8 {
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    v___x_3318_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_3316_);
    v___x_3319_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_y_3317_);
    v___x_3320_ = lean_nat_dec_lt(v___x_3318_, v___x_3319_);
    if v___x_3320_ == 0 {
        let mut v___x_3321_: u8 = 0;
        v___x_3321_ = lean_nat_dec_eq(v___x_3318_, v___x_3319_);
        leanh::lean_dec(v___x_3319_);
        leanh::lean_dec(v___x_3318_);
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
        leanh::lean_dec(v___x_3319_);
        leanh::lean_dec(v___x_3318_);
        v___x_3324_ = 0;
        return v___x_3324_;
    }
}
pub unsafe fn l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed(
    mut v_x_3325_: *mut leanh::LeanObject,
    mut v_y_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_30__boxed_3327_: u8 = 0;
    let mut v_y_31__boxed_3328_: u8 = 0;
    let mut v_res_3329_: u8 = 0;
    let mut v_r_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_3327_ = (leanh::lean_unbox(v_x_3325_) as u8);
    v_y_31__boxed_3328_ = (leanh::lean_unbox(v_y_3326_) as u8);
    v_res_3329_ = l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(v_x_30__boxed_3327_, v_y_31__boxed_3328_);
    v_r_3330_ = leanh::lean_box((v_res_3329_) as usize);
    return v_r_3330_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0(
    mut v_j_3342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: u8 = 0;
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: u8 = 0;
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3345_ = l_Lean_Json_getNat_x3f(v_j_3342_);
                if leanh::lean_obj_tag(v___x_3345_) == 1 {
                    v_a_3346_ = leanh::lean_ctor_get(v___x_3345_, 0);
                    leanh::lean_inc(v_a_3346_);
                    leanh::lean_dec_ref_known(v___x_3345_, 1);
                    v___x_3347_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3348_ = lean_nat_dec_eq(v_a_3346_, v___x_3347_);
                    if v___x_3348_ == 0 {
                        v___x_3349_ = leanh::lean_unsigned_to_nat(2);
                        v___x_3350_ = lean_nat_dec_eq(v_a_3346_, v___x_3349_);
                        leanh::lean_dec(v_a_3346_);
                        if v___x_3350_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_3351_ =
                                l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2;
                            return v___x_3351_;
                        }
                    } else {
                        leanh::lean_dec(v_a_3346_);
                        v___x_3352_ = l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3;
                        return v___x_3352_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3345_);
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
) -> *mut leanh::LeanObject {
    if v_x_3355_ == 0 {
        let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3356_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once
            ),
            _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1,
        );
        return v___x_3356_;
    } else {
        let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3357_ = leanh::lean_obj_once(
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
    mut v_x_3358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_48__boxed_3359_: u8 = 0;
    let mut v_res_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_48__boxed_3359_ = (leanh::lean_unbox(v_x_3358_) as u8);
    v_res_3360_ = l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(v_x_48__boxed_3359_);
    return v_res_3360_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3364_ = l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0;
    v___x_3365_ = l_Lean_Lsp_instInhabitedLocation_default;
    v___x_3366_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3366_, 0, v___x_3365_);
    leanh::lean_ctor_set(v___x_3366_, 1, v___x_3364_);
    return v___x_3366_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default()
-> *mut leanh::LeanObject {
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3367_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3368_ = l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default;
    return v___x_3368_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(
    mut v_x_3369_: *mut leanh::LeanObject,
    mut v_x_3370_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_location_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_location_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: u8 = 0;
    v_location_3371_ = leanh::lean_ctor_get(v_x_3369_, 0);
    v_message_3372_ = leanh::lean_ctor_get(v_x_3369_, 1);
    v_location_3373_ = leanh::lean_ctor_get(v_x_3370_, 0);
    v_message_3374_ = leanh::lean_ctor_get(v_x_3370_, 1);
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
    mut v_x_3377_: *mut leanh::LeanObject,
    mut v_x_3378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3379_: u8 = 0;
    let mut v_r_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3379_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(v_x_3377_, v_x_3378_);
    leanh::lean_dec_ref(v_x_3378_);
    leanh::lean_dec_ref(v_x_3377_);
    v_r_3380_ = leanh::lean_box((v_res_3379_) as usize);
    return v_r_3380_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(
    mut v_a_3383_: *mut leanh::LeanObject,
    mut v_a_3384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3383_) == 0 {
                    v___x_3385_ = lean_array_to_list(v_a_3384_);
                    return v___x_3385_;
                } else {
                    v_head_3386_ = leanh::lean_ctor_get(v_a_3383_, 0);
                    leanh::lean_inc(v_head_3386_);
                    v_tail_3387_ = leanh::lean_ctor_get(v_a_3383_, 1);
                    leanh::lean_inc(v_tail_3387_);
                    leanh::lean_dec_ref_known(v_a_3383_, 2);
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
    mut v_x_3394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_location_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3399_: u8 = 0;
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_location_3395_ = leanh::lean_ctor_get(v_x_3394_, 0);
                v_message_3396_ = leanh::lean_ctor_get(v_x_3394_, 1);
                v_isSharedCheck_3416_ = (!leanh::lean_is_exclusive(v_x_3394_)) as u8;
                if v_isSharedCheck_3416_ == 0 {
                    v___x_3398_ = v_x_3394_;
                    v_isShared_3399_ = v_isSharedCheck_3416_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_message_3396_);
                    leanh::lean_inc(v_location_3395_);
                    leanh::lean_dec(v_x_3394_);
                    v___x_3398_ = leanh::lean_box(0);
                    v_isShared_3399_ = v_isSharedCheck_3416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3400_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0;
                v___x_3401_ = l_Lean_Lsp_instToJsonLocation_toJson(v_location_3395_);
                if v_isShared_3399_ == 0 {
                    leanh::lean_ctor_set(v___x_3398_, 1, v___x_3401_);
                    leanh::lean_ctor_set(v___x_3398_, 0, v___x_3400_);
                    v___x_3403_ = v___x_3398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3415_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3415_, 1, v___x_3401_);
                    v___x_3403_ = v_reuseFailAlloc_3415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3404_ = leanh::lean_box(0);
                v___x_3405_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3405_, 0, v___x_3403_);
                leanh::lean_ctor_set(v___x_3405_, 1, v___x_3404_);
                v___x_3406_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
                v___x_3407_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3407_, 0, v_message_3396_);
                v___x_3408_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3408_, 0, v___x_3406_);
                leanh::lean_ctor_set(v___x_3408_, 1, v___x_3407_);
                v___x_3409_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3409_, 0, v___x_3408_);
                leanh::lean_ctor_set(v___x_3409_, 1, v___x_3404_);
                v___x_3410_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3410_, 0, v___x_3409_);
                leanh::lean_ctor_set(v___x_3410_, 1, v___x_3404_);
                v___x_3411_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3411_, 0, v___x_3405_);
                leanh::lean_ctor_set(v___x_3411_, 1, v___x_3410_);
                v___x_3412_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2;
                v___x_3413_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_3411_, v___x_3412_);
                v___x_3414_ = l_Lean_Json_mkObj(v___x_3413_);
                leanh::lean_dec(v___x_3413_);
                return v___x_3414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(
    mut v_j_3419_: *mut leanh::LeanObject,
    mut v_k_3420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ = l_Lean_Json_getObjValD(v_j_3419_, v_k_3420_);
    v___x_3422_ = l_Lean_Lsp_instFromJsonLocation_fromJson(v___x_3421_);
    return v___x_3422_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0___boxed(
    mut v_j_3423_: *mut leanh::LeanObject,
    mut v_k_3424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_j_3423_, v_k_3424_);
    leanh::lean_dec_ref(v_k_3424_);
    return v_res_3425_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(
    mut v_j_3426_: *mut leanh::LeanObject,
    mut v_k_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3428_ = l_Lean_Json_getObjValD(v_j_3426_, v_k_3427_);
    v___x_3429_ = l_Lean_Json_getStr_x3f(v___x_3428_);
    return v___x_3429_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1___boxed(
    mut v_j_3430_: *mut leanh::LeanObject,
    mut v_k_3431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_j_3430_, v_k_3431_);
    leanh::lean_dec_ref(v_k_3431_);
    return v_res_3432_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3440_: u8 = 0;
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3440_ = 1;
    v___x_3441_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3;
    v___x_3442_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3441_, v___x_3440_);
    return v___x_3442_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3444_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5;
    v___x_3445_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3449_ = 1;
    v___x_3450_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7;
    v___x_3451_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3450_, v___x_3449_);
    return v___x_3451_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3452_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8,
    );
    v___x_3453_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3457_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3461_ = 1;
    v___x_3462_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12;
    v___x_3463_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3462_, v___x_3461_);
    return v___x_3463_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13,
    );
    v___x_3465_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3467_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3468_ = leanh::lean_obj_once(
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
    mut v_json_3470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut v_a_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3490_: u8 = 0;
    let mut v_a_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3497_: u8 = 0;
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3503_: u8 = 0;
    let mut v_a_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3507_: u8 = 0;
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3511_: u8 = 0;
    let mut v_a_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3471_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0;
                leanh::lean_inc(v_json_3470_);
                v___x_3472_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_json_3470_, v___x_3471_);
                if leanh::lean_obj_tag(v___x_3472_) == 0 {
                    leanh::lean_dec(v_json_3470_);
                    v_a_3473_ = leanh::lean_ctor_get(v___x_3472_, 0);
                    v_isSharedCheck_3482_ = (!leanh::lean_is_exclusive(v___x_3472_)) as u8;
                    if v_isSharedCheck_3482_ == 0 {
                        v___x_3475_ = v___x_3472_;
                        v_isShared_3476_ = v_isSharedCheck_3482_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3473_);
                        leanh::lean_dec(v___x_3472_);
                        v___x_3475_ = leanh::lean_box(0);
                        v_isShared_3476_ = v_isSharedCheck_3482_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_3472_) == 0 {
                        leanh::lean_dec(v_json_3470_);
                        v_a_3483_ = leanh::lean_ctor_get(v___x_3472_, 0);
                        v_isSharedCheck_3490_ =
                            (!leanh::lean_is_exclusive(v___x_3472_)) as u8;
                        if v_isSharedCheck_3490_ == 0 {
                            v___x_3485_ = v___x_3472_;
                            v_isShared_3486_ = v_isSharedCheck_3490_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3483_);
                            leanh::lean_dec(v___x_3472_);
                            v___x_3485_ = leanh::lean_box(0);
                            v_isShared_3486_ = v_isSharedCheck_3490_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3491_ = leanh::lean_ctor_get(v___x_3472_, 0);
                        leanh::lean_inc(v_a_3491_);
                        leanh::lean_dec_ref_known(v___x_3472_, 1);
                        v___x_3492_ =
                            l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
                        v___x_3493_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_3470_, v___x_3492_);
                        if leanh::lean_obj_tag(v___x_3493_) == 0 {
                            leanh::lean_dec(v_a_3491_);
                            v_a_3494_ = leanh::lean_ctor_get(v___x_3493_, 0);
                            v_isSharedCheck_3503_ =
                                (!leanh::lean_is_exclusive(v___x_3493_)) as u8;
                            if v_isSharedCheck_3503_ == 0 {
                                v___x_3496_ = v___x_3493_;
                                v_isShared_3497_ = v_isSharedCheck_3503_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3494_);
                                leanh::lean_dec(v___x_3493_);
                                v___x_3496_ = leanh::lean_box(0);
                                v_isShared_3497_ = v_isSharedCheck_3503_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_3493_) == 0 {
                                leanh::lean_dec(v_a_3491_);
                                v_a_3504_ = leanh::lean_ctor_get(v___x_3493_, 0);
                                v_isSharedCheck_3511_ =
                                    (!leanh::lean_is_exclusive(v___x_3493_)) as u8;
                                if v_isSharedCheck_3511_ == 0 {
                                    v___x_3506_ = v___x_3493_;
                                    v_isShared_3507_ = v_isSharedCheck_3511_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3504_);
                                    leanh::lean_dec(v___x_3493_);
                                    v___x_3506_ = leanh::lean_box(0);
                                    v_isShared_3507_ = v_isSharedCheck_3511_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3512_ = leanh::lean_ctor_get(v___x_3493_, 0);
                                v_isSharedCheck_3520_ =
                                    (!leanh::lean_is_exclusive(v___x_3493_)) as u8;
                                if v_isSharedCheck_3520_ == 0 {
                                    v___x_3514_ = v___x_3493_;
                                    v_isShared_3515_ = v_isSharedCheck_3520_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3512_);
                                    leanh::lean_dec(v___x_3493_);
                                    v___x_3514_ = leanh::lean_box(0);
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
                v___x_3477_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once), _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11);
                v___x_3478_ = lean_string_append(v___x_3477_, v_a_3473_);
                leanh::lean_dec(v_a_3473_);
                if v_isShared_3476_ == 0 {
                    leanh::lean_ctor_set(v___x_3475_, 0, v___x_3478_);
                    v___x_3480_ = v___x_3475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3481_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
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
                    leanh::lean_ctor_set_tag(v___x_3485_, 0);
                    v___x_3488_ = v___x_3485_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3489_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
                    v___x_3488_ = v_reuseFailAlloc_3489_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3488_;
            }
            5 => {
                v___x_3498_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once), _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15);
                v___x_3499_ = lean_string_append(v___x_3498_, v_a_3494_);
                leanh::lean_dec(v_a_3494_);
                if v_isShared_3497_ == 0 {
                    leanh::lean_ctor_set(v___x_3496_, 0, v___x_3499_);
                    v___x_3501_ = v___x_3496_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3502_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
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
                    leanh::lean_ctor_set_tag(v___x_3506_, 0);
                    v___x_3509_ = v___x_3506_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3510_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
                    v___x_3509_ = v_reuseFailAlloc_3510_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3509_;
            }
            9 => {
                v___x_3516_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3516_, 0, v_a_3491_);
                leanh::lean_ctor_set(v___x_3516_, 1, v_a_3512_);
                if v_isShared_3515_ == 0 {
                    leanh::lean_ctor_set(v___x_3514_, 0, v___x_3516_);
                    v___x_3518_ = v___x_3514_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
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
    mut v_x_3523_: *mut leanh::LeanObject,
    mut v_x_3524_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_location_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_location_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    v_location_3525_ = leanh::lean_ctor_get(v_x_3523_, 0);
    v_message_3526_ = leanh::lean_ctor_get(v_x_3523_, 1);
    v_location_3527_ = leanh::lean_ctor_get(v_x_3524_, 0);
    v_message_3528_ = leanh::lean_ctor_get(v_x_3524_, 1);
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
    mut v_x_3531_: *mut leanh::LeanObject,
    mut v_x_3532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3533_: u8 = 0;
    let mut v_r_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3533_ = l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(v_x_3531_, v_x_3532_);
    leanh::lean_dec_ref(v_x_3532_);
    leanh::lean_dec_ref(v_x_3531_);
    v_r_3534_ = leanh::lean_box((v_res_3533_) as usize);
    return v_r_3534_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3537_ = l_Lean_Lsp_instInhabitedRange_default;
    v___x_3538_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3538_, 0, v___x_3537_);
    return v___x_3538_;
}
pub unsafe fn l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(
    mut v_inst_3539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3540_ = l_Lean_Lsp_instInhabitedRange_default;
    v___x_3541_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once
        ),
        _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0,
    );
    v___x_3542_ = leanh::lean_box(0);
    v___x_3543_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
    leanh::lean_ctor_set(v___x_3543_, 0, v___x_3540_);
    leanh::lean_ctor_set(v___x_3543_, 1, v___x_3541_);
    leanh::lean_ctor_set(v___x_3543_, 2, v___x_3542_);
    leanh::lean_ctor_set(v___x_3543_, 3, v___x_3542_);
    leanh::lean_ctor_set(v___x_3543_, 4, v___x_3542_);
    leanh::lean_ctor_set(v___x_3543_, 5, v___x_3542_);
    leanh::lean_ctor_set(v___x_3543_, 6, v_inst_3539_);
    leanh::lean_ctor_set(v___x_3543_, 7, v___x_3542_);
    leanh::lean_ctor_set(v___x_3543_, 8, v___x_3542_);
    leanh::lean_ctor_set(v___x_3543_, 9, v___x_3542_);
    leanh::lean_ctor_set(v___x_3543_, 10, v___x_3542_);
    return v___x_3543_;
}
pub unsafe fn l_Lean_Lsp_instInhabitedDiagnosticWith_default(
    mut v_00_u03b1_3544_: *mut leanh::LeanObject,
    mut v_inst_3545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3546_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_3545_);
    return v___x_3546_;
}
pub unsafe fn l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(
    mut v_inst_3547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3548_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_3547_);
    return v___x_3548_;
}
pub unsafe fn l_Lean_Lsp_instInhabitedDiagnosticWith(
    mut v_a_3549_: *mut leanh::LeanObject,
    mut v_inst_3550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3551_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_3550_);
    return v___x_3551_;
}
pub unsafe fn _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = leanh::lean_alloc_closure(
        l_instDecidableEqBool___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_3554_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3554_, 0, v___x_3553_);
    return v___f_3554_;
}
pub unsafe fn _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3555_ = leanh::lean_alloc_closure(
        l_instDecidableEqString___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_3556_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3556_, 0, v___x_3555_);
    return v___f_3556_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(
    mut v_inst_3564_: *mut leanh::LeanObject,
    mut v_x_3565_: *mut leanh::LeanObject,
    mut v_x_3566_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_range_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: u8 = 0;
    v_range_3567_ = leanh::lean_ctor_get(v_x_3565_, 0);
    leanh::lean_inc_ref(v_range_3567_);
    v_fullRange_x3f_3568_ = leanh::lean_ctor_get(v_x_3565_, 1);
    leanh::lean_inc(v_fullRange_x3f_3568_);
    v_severity_x3f_3569_ = leanh::lean_ctor_get(v_x_3565_, 2);
    leanh::lean_inc(v_severity_x3f_3569_);
    v_isSilent_x3f_3570_ = leanh::lean_ctor_get(v_x_3565_, 3);
    leanh::lean_inc(v_isSilent_x3f_3570_);
    v_code_x3f_3571_ = leanh::lean_ctor_get(v_x_3565_, 4);
    leanh::lean_inc(v_code_x3f_3571_);
    v_source_x3f_3572_ = leanh::lean_ctor_get(v_x_3565_, 5);
    leanh::lean_inc(v_source_x3f_3572_);
    v_message_3573_ = leanh::lean_ctor_get(v_x_3565_, 6);
    leanh::lean_inc(v_message_3573_);
    v_tags_x3f_3574_ = leanh::lean_ctor_get(v_x_3565_, 7);
    leanh::lean_inc(v_tags_x3f_3574_);
    v_leanTags_x3f_3575_ = leanh::lean_ctor_get(v_x_3565_, 8);
    leanh::lean_inc(v_leanTags_x3f_3575_);
    v_relatedInformation_x3f_3576_ = leanh::lean_ctor_get(v_x_3565_, 9);
    leanh::lean_inc(v_relatedInformation_x3f_3576_);
    v_data_x3f_3577_ = leanh::lean_ctor_get(v_x_3565_, 10);
    leanh::lean_inc(v_data_x3f_3577_);
    leanh::lean_dec_ref(v_x_3565_);
    v_range_3578_ = leanh::lean_ctor_get(v_x_3566_, 0);
    leanh::lean_inc_ref(v_range_3578_);
    v_fullRange_x3f_3579_ = leanh::lean_ctor_get(v_x_3566_, 1);
    leanh::lean_inc(v_fullRange_x3f_3579_);
    v_severity_x3f_3580_ = leanh::lean_ctor_get(v_x_3566_, 2);
    leanh::lean_inc(v_severity_x3f_3580_);
    v_isSilent_x3f_3581_ = leanh::lean_ctor_get(v_x_3566_, 3);
    leanh::lean_inc(v_isSilent_x3f_3581_);
    v_code_x3f_3582_ = leanh::lean_ctor_get(v_x_3566_, 4);
    leanh::lean_inc(v_code_x3f_3582_);
    v_source_x3f_3583_ = leanh::lean_ctor_get(v_x_3566_, 5);
    leanh::lean_inc(v_source_x3f_3583_);
    v_message_3584_ = leanh::lean_ctor_get(v_x_3566_, 6);
    leanh::lean_inc(v_message_3584_);
    v_tags_x3f_3585_ = leanh::lean_ctor_get(v_x_3566_, 7);
    leanh::lean_inc(v_tags_x3f_3585_);
    v_leanTags_x3f_3586_ = leanh::lean_ctor_get(v_x_3566_, 8);
    leanh::lean_inc(v_leanTags_x3f_3586_);
    v_relatedInformation_x3f_3587_ = leanh::lean_ctor_get(v_x_3566_, 9);
    leanh::lean_inc(v_relatedInformation_x3f_3587_);
    v_data_x3f_3588_ = leanh::lean_ctor_get(v_x_3566_, 10);
    leanh::lean_inc(v_data_x3f_3588_);
    leanh::lean_dec_ref(v_x_3566_);
    v___x_3589_ = l_Lean_Lsp_instBEqRange_beq(v_range_3567_, v_range_3578_);
    leanh::lean_dec_ref(v_range_3578_);
    leanh::lean_dec_ref(v_range_3567_);
    if v___x_3589_ == 0 {
        leanh::lean_dec(v_data_x3f_3588_);
        leanh::lean_dec(v_relatedInformation_x3f_3587_);
        leanh::lean_dec(v_leanTags_x3f_3586_);
        leanh::lean_dec(v_tags_x3f_3585_);
        leanh::lean_dec(v_message_3584_);
        leanh::lean_dec(v_source_x3f_3583_);
        leanh::lean_dec(v_code_x3f_3582_);
        leanh::lean_dec(v_isSilent_x3f_3581_);
        leanh::lean_dec(v_severity_x3f_3580_);
        leanh::lean_dec(v_fullRange_x3f_3579_);
        leanh::lean_dec(v_data_x3f_3577_);
        leanh::lean_dec(v_relatedInformation_x3f_3576_);
        leanh::lean_dec(v_leanTags_x3f_3575_);
        leanh::lean_dec(v_tags_x3f_3574_);
        leanh::lean_dec(v_message_3573_);
        leanh::lean_dec(v_source_x3f_3572_);
        leanh::lean_dec(v_code_x3f_3571_);
        leanh::lean_dec(v_isSilent_x3f_3570_);
        leanh::lean_dec(v_severity_x3f_3569_);
        leanh::lean_dec(v_fullRange_x3f_3568_);
        leanh::lean_dec_ref(v_inst_3564_);
        return v___x_3589_;
    } else {
        let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3591_: u8 = 0;
        v___x_3590_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0;
        v___x_3591_ = l_Option_instBEq_beq___redArg(
            v___x_3590_,
            v_fullRange_x3f_3568_,
            v_fullRange_x3f_3579_,
        );
        if v___x_3591_ == 0 {
            leanh::lean_dec(v_data_x3f_3588_);
            leanh::lean_dec(v_relatedInformation_x3f_3587_);
            leanh::lean_dec(v_leanTags_x3f_3586_);
            leanh::lean_dec(v_tags_x3f_3585_);
            leanh::lean_dec(v_message_3584_);
            leanh::lean_dec(v_source_x3f_3583_);
            leanh::lean_dec(v_code_x3f_3582_);
            leanh::lean_dec(v_isSilent_x3f_3581_);
            leanh::lean_dec(v_severity_x3f_3580_);
            leanh::lean_dec(v_data_x3f_3577_);
            leanh::lean_dec(v_relatedInformation_x3f_3576_);
            leanh::lean_dec(v_leanTags_x3f_3575_);
            leanh::lean_dec(v_tags_x3f_3574_);
            leanh::lean_dec(v_message_3573_);
            leanh::lean_dec(v_source_x3f_3572_);
            leanh::lean_dec(v_code_x3f_3571_);
            leanh::lean_dec(v_isSilent_x3f_3570_);
            leanh::lean_dec(v_severity_x3f_3569_);
            leanh::lean_dec_ref(v_inst_3564_);
            return v___x_3591_;
        } else {
            let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3593_: u8 = 0;
            v___x_3592_ = l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0;
            v___x_3593_ = l_Option_instBEq_beq___redArg(
                v___x_3592_,
                v_severity_x3f_3569_,
                v_severity_x3f_3580_,
            );
            if v___x_3593_ == 0 {
                leanh::lean_dec(v_data_x3f_3588_);
                leanh::lean_dec(v_relatedInformation_x3f_3587_);
                leanh::lean_dec(v_leanTags_x3f_3586_);
                leanh::lean_dec(v_tags_x3f_3585_);
                leanh::lean_dec(v_message_3584_);
                leanh::lean_dec(v_source_x3f_3583_);
                leanh::lean_dec(v_code_x3f_3582_);
                leanh::lean_dec(v_isSilent_x3f_3581_);
                leanh::lean_dec(v_data_x3f_3577_);
                leanh::lean_dec(v_relatedInformation_x3f_3576_);
                leanh::lean_dec(v_leanTags_x3f_3575_);
                leanh::lean_dec(v_tags_x3f_3574_);
                leanh::lean_dec(v_message_3573_);
                leanh::lean_dec(v_source_x3f_3572_);
                leanh::lean_dec(v_code_x3f_3571_);
                leanh::lean_dec(v_isSilent_x3f_3570_);
                leanh::lean_dec_ref(v_inst_3564_);
                return v___x_3593_;
            } else {
                let mut v___f_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3595_: u8 = 0;
                v___f_3594_ = leanh::lean_obj_once(
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
                    leanh::lean_dec(v_data_x3f_3588_);
                    leanh::lean_dec(v_relatedInformation_x3f_3587_);
                    leanh::lean_dec(v_leanTags_x3f_3586_);
                    leanh::lean_dec(v_tags_x3f_3585_);
                    leanh::lean_dec(v_message_3584_);
                    leanh::lean_dec(v_source_x3f_3583_);
                    leanh::lean_dec(v_code_x3f_3582_);
                    leanh::lean_dec(v_data_x3f_3577_);
                    leanh::lean_dec(v_relatedInformation_x3f_3576_);
                    leanh::lean_dec(v_leanTags_x3f_3575_);
                    leanh::lean_dec(v_tags_x3f_3574_);
                    leanh::lean_dec(v_message_3573_);
                    leanh::lean_dec(v_source_x3f_3572_);
                    leanh::lean_dec(v_code_x3f_3571_);
                    leanh::lean_dec_ref(v_inst_3564_);
                    return v___x_3595_;
                } else {
                    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3597_: u8 = 0;
                    v___x_3596_ = l_Lean_Lsp_instBEqDiagnosticCode___closed__0;
                    v___x_3597_ = l_Option_instBEq_beq___redArg(
                        v___x_3596_,
                        v_code_x3f_3571_,
                        v_code_x3f_3582_,
                    );
                    if v___x_3597_ == 0 {
                        leanh::lean_dec(v_data_x3f_3588_);
                        leanh::lean_dec(v_relatedInformation_x3f_3587_);
                        leanh::lean_dec(v_leanTags_x3f_3586_);
                        leanh::lean_dec(v_tags_x3f_3585_);
                        leanh::lean_dec(v_message_3584_);
                        leanh::lean_dec(v_source_x3f_3583_);
                        leanh::lean_dec(v_data_x3f_3577_);
                        leanh::lean_dec(v_relatedInformation_x3f_3576_);
                        leanh::lean_dec(v_leanTags_x3f_3575_);
                        leanh::lean_dec(v_tags_x3f_3574_);
                        leanh::lean_dec(v_message_3573_);
                        leanh::lean_dec(v_source_x3f_3572_);
                        leanh::lean_dec_ref(v_inst_3564_);
                        return v___x_3597_;
                    } else {
                        let mut v___f_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3599_: u8 = 0;
                        v___f_3598_ = leanh::lean_obj_once(
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
                            leanh::lean_dec(v_data_x3f_3588_);
                            leanh::lean_dec(v_relatedInformation_x3f_3587_);
                            leanh::lean_dec(v_leanTags_x3f_3586_);
                            leanh::lean_dec(v_tags_x3f_3585_);
                            leanh::lean_dec(v_message_3584_);
                            leanh::lean_dec(v_data_x3f_3577_);
                            leanh::lean_dec(v_relatedInformation_x3f_3576_);
                            leanh::lean_dec(v_leanTags_x3f_3575_);
                            leanh::lean_dec(v_tags_x3f_3574_);
                            leanh::lean_dec(v_message_3573_);
                            leanh::lean_dec_ref(v_inst_3564_);
                            return v___x_3599_;
                        } else {
                            let mut v___x_3600_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3601_: u8 = 0;
                            v___x_3600_ = leanh::lean_apply_2(
                                v_inst_3564_,
                                v_message_3573_,
                                v_message_3584_,
                            );
                            v___x_3601_ = (leanh::lean_unbox(v___x_3600_) as u8);
                            if v___x_3601_ == 0 {
                                let mut v___x_3602_: u8 = 0;
                                leanh::lean_dec(v_data_x3f_3588_);
                                leanh::lean_dec(v_relatedInformation_x3f_3587_);
                                leanh::lean_dec(v_leanTags_x3f_3586_);
                                leanh::lean_dec(v_tags_x3f_3585_);
                                leanh::lean_dec(v_data_x3f_3577_);
                                leanh::lean_dec(v_relatedInformation_x3f_3576_);
                                leanh::lean_dec(v_leanTags_x3f_3575_);
                                leanh::lean_dec(v_tags_x3f_3574_);
                                v___x_3602_ = (leanh::lean_unbox(v___x_3600_) as u8);
                                return v___x_3602_;
                            } else {
                                let mut v___f_3603_: *mut leanh::LeanObject =
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
                                    leanh::lean_dec(v_data_x3f_3588_);
                                    leanh::lean_dec(v_relatedInformation_x3f_3587_);
                                    leanh::lean_dec(v_leanTags_x3f_3586_);
                                    leanh::lean_dec(v_data_x3f_3577_);
                                    leanh::lean_dec(v_relatedInformation_x3f_3576_);
                                    leanh::lean_dec(v_leanTags_x3f_3575_);
                                    return v___x_3604_;
                                } else {
                                    let mut v___f_3605_: *mut leanh::LeanObject =
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
                                        leanh::lean_dec(v_data_x3f_3588_);
                                        leanh::lean_dec(v_relatedInformation_x3f_3587_);
                                        leanh::lean_dec(v_data_x3f_3577_);
                                        leanh::lean_dec(v_relatedInformation_x3f_3576_);
                                        return v___x_3606_;
                                    } else {
                                        let mut v___f_3607_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3608_: u8 = 0;
                                        v___f_3607_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5;
                                        v___x_3608_ = l_Option_instBEq_beq___redArg(
                                            v___f_3607_,
                                            v_relatedInformation_x3f_3576_,
                                            v_relatedInformation_x3f_3587_,
                                        );
                                        if v___x_3608_ == 0 {
                                            leanh::lean_dec(v_data_x3f_3588_);
                                            leanh::lean_dec(v_data_x3f_3577_);
                                            return v___x_3608_;
                                        } else {
                                            let mut v___x_3609_: *mut leanh::LeanObject =
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
    mut v_inst_3611_: *mut leanh::LeanObject,
    mut v_x_3612_: *mut leanh::LeanObject,
    mut v_x_3613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3614_: u8 = 0;
    let mut v_r_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3614_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_3611_, v_x_3612_, v_x_3613_);
    v_r_3615_ = leanh::lean_box((v_res_3614_) as usize);
    return v_r_3615_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq(
    mut v_00_u03b1_3616_: *mut leanh::LeanObject,
    mut v_inst_3617_: *mut leanh::LeanObject,
    mut v_x_3618_: *mut leanh::LeanObject,
    mut v_x_3619_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3620_: u8 = 0;
    v___x_3620_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_3617_, v_x_3618_, v_x_3619_);
    return v___x_3620_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(
    mut v_00_u03b1_3621_: *mut leanh::LeanObject,
    mut v_inst_3622_: *mut leanh::LeanObject,
    mut v_x_3623_: *mut leanh::LeanObject,
    mut v_x_3624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3625_: u8 = 0;
    let mut v_r_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3625_ =
        l_Lean_Lsp_instBEqDiagnosticWith_beq(v_00_u03b1_3621_, v_inst_3622_, v_x_3623_, v_x_3624_);
    v_r_3626_ = leanh::lean_box((v_res_3625_) as usize);
    return v_r_3626_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith___redArg(
    mut v_inst_3627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3628_ = leanh::lean_alloc_closure(
        l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_3628_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3628_, 1, v_inst_3627_);
    return v___x_3628_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith(
    mut v_00_u03b1_3629_: *mut leanh::LeanObject,
    mut v_inst_3630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3631_ = leanh::lean_alloc_closure(
        l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_3631_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3631_, 1, v_inst_3630_);
    return v___x_3631_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(
    mut v_inst_3652_: *mut leanh::LeanObject,
    mut v_x_3653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_3654_ = leanh::lean_ctor_get(v_x_3653_, 0);
    leanh::lean_inc_ref(v_range_3654_);
    v_fullRange_x3f_3655_ = leanh::lean_ctor_get(v_x_3653_, 1);
    leanh::lean_inc(v_fullRange_x3f_3655_);
    v_severity_x3f_3656_ = leanh::lean_ctor_get(v_x_3653_, 2);
    leanh::lean_inc(v_severity_x3f_3656_);
    v_isSilent_x3f_3657_ = leanh::lean_ctor_get(v_x_3653_, 3);
    leanh::lean_inc(v_isSilent_x3f_3657_);
    v_code_x3f_3658_ = leanh::lean_ctor_get(v_x_3653_, 4);
    leanh::lean_inc(v_code_x3f_3658_);
    v_source_x3f_3659_ = leanh::lean_ctor_get(v_x_3653_, 5);
    leanh::lean_inc(v_source_x3f_3659_);
    v_message_3660_ = leanh::lean_ctor_get(v_x_3653_, 6);
    leanh::lean_inc(v_message_3660_);
    v_tags_x3f_3661_ = leanh::lean_ctor_get(v_x_3653_, 7);
    leanh::lean_inc(v_tags_x3f_3661_);
    v_leanTags_x3f_3662_ = leanh::lean_ctor_get(v_x_3653_, 8);
    leanh::lean_inc(v_leanTags_x3f_3662_);
    v_relatedInformation_x3f_3663_ = leanh::lean_ctor_get(v_x_3653_, 9);
    leanh::lean_inc(v_relatedInformation_x3f_3663_);
    v_data_x3f_3664_ = leanh::lean_ctor_get(v_x_3653_, 10);
    leanh::lean_inc(v_data_x3f_3664_);
    leanh::lean_dec_ref(v_x_3653_);
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
    v___x_3676_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3676_, 0, v___x_3674_);
    leanh::lean_ctor_set(v___x_3676_, 1, v___x_3675_);
    v___x_3677_ = leanh::lean_box(0);
    v___x_3678_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3678_, 0, v___x_3676_);
    leanh::lean_ctor_set(v___x_3678_, 1, v___x_3677_);
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
    v___x_3690_ = leanh::lean_apply_1(v_inst_3652_, v_message_3660_);
    v___x_3691_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3691_, 0, v___x_3689_);
    leanh::lean_ctor_set(v___x_3691_, 1, v___x_3690_);
    v___x_3692_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3692_, 0, v___x_3691_);
    leanh::lean_ctor_set(v___x_3692_, 1, v___x_3677_);
    v___x_3693_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13;
    v___x_3694_ = l_Lean_Json_opt___redArg(v___x_3670_, v___x_3693_, v_tags_x3f_3661_);
    v___x_3695_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14;
    v___x_3696_ = l_Lean_Json_opt___redArg(v___x_3671_, v___x_3695_, v_leanTags_x3f_3662_);
    v___x_3697_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15;
    v___x_3698_ =
        l_Lean_Json_opt___redArg(v___x_3672_, v___x_3697_, v_relatedInformation_x3f_3663_);
    v___x_3699_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16;
    v___x_3700_ = l_Lean_Json_opt___redArg(v___x_3673_, v___x_3699_, v_data_x3f_3664_);
    v___x_3701_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3701_, 0, v___x_3700_);
    leanh::lean_ctor_set(v___x_3701_, 1, v___x_3677_);
    v___x_3702_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3702_, 0, v___x_3698_);
    leanh::lean_ctor_set(v___x_3702_, 1, v___x_3701_);
    v___x_3703_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3703_, 0, v___x_3696_);
    leanh::lean_ctor_set(v___x_3703_, 1, v___x_3702_);
    v___x_3704_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3704_, 0, v___x_3694_);
    leanh::lean_ctor_set(v___x_3704_, 1, v___x_3703_);
    v___x_3705_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3705_, 0, v___x_3692_);
    leanh::lean_ctor_set(v___x_3705_, 1, v___x_3704_);
    v___x_3706_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3706_, 0, v___x_3688_);
    leanh::lean_ctor_set(v___x_3706_, 1, v___x_3705_);
    v___x_3707_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3707_, 0, v___x_3686_);
    leanh::lean_ctor_set(v___x_3707_, 1, v___x_3706_);
    v___x_3708_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3708_, 0, v___x_3684_);
    leanh::lean_ctor_set(v___x_3708_, 1, v___x_3707_);
    v___x_3709_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3709_, 0, v___x_3682_);
    leanh::lean_ctor_set(v___x_3709_, 1, v___x_3708_);
    v___x_3710_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3710_, 0, v___x_3680_);
    leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
    v___x_3711_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3711_, 0, v___x_3678_);
    leanh::lean_ctor_set(v___x_3711_, 1, v___x_3710_);
    v___x_3712_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2;
    v___x_3713_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3673_,
        v___x_3711_,
        v___x_3712_,
    );
    v___x_3714_ = l_Lean_Json_mkObj(v___x_3713_);
    leanh::lean_dec(v___x_3713_);
    return v___x_3714_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith_toJson(
    mut v_00_u03b1_3715_: *mut leanh::LeanObject,
    mut v_inst_3716_: *mut leanh::LeanObject,
    mut v_x_3717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3718_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(v_inst_3716_, v_x_3717_);
    return v___x_3718_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith___redArg(
    mut v_inst_3719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ = leanh::lean_alloc_closure(
        l_Lean_Lsp_instToJsonDiagnosticWith_toJson as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_3720_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3720_, 1, v_inst_3719_);
    return v___x_3720_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith(
    mut v_00_u03b1_3721_: *mut leanh::LeanObject,
    mut v_inst_3722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = leanh::lean_alloc_closure(
        l_Lean_Lsp_instToJsonDiagnosticWith_toJson as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_3723_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3723_, 1, v_inst_3722_);
    return v___x_3723_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3732_: u8 = 0;
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3732_ = 1;
    v___x_3733_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3;
    v___x_3734_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3733_, v___x_3732_);
    return v___x_3734_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5;
    v___x_3736_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3740_ = 1;
    v___x_3741_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6;
    v___x_3742_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3741_, v___x_3740_);
    return v___x_3742_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3743_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7,
    );
    v___x_3744_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3746_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3747_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3752_: u8 = 0;
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3752_ = 1;
    v___x_3753_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11;
    v___x_3754_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3753_, v___x_3752_);
    return v___x_3754_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3755_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12,
    );
    v___x_3756_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3758_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3759_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3766_: u8 = 0;
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3766_ = 1;
    v___x_3767_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17;
    v___x_3768_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3767_, v___x_3766_);
    return v___x_3768_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3769_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18,
    );
    v___x_3770_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3772_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3773_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3781_: u8 = 0;
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3781_ = 1;
    v___x_3782_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24;
    v___x_3783_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3782_, v___x_3781_);
    return v___x_3783_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3784_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25,
    );
    v___x_3785_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3787_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3788_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3795_: u8 = 0;
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3795_ = 1;
    v___x_3796_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30;
    v___x_3797_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3796_, v___x_3795_);
    return v___x_3797_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3798_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31,
    );
    v___x_3799_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3801_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3802_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3810_: u8 = 0;
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3810_ = 1;
    v___x_3811_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37;
    v___x_3812_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3811_, v___x_3810_);
    return v___x_3812_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3813_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38,
    );
    v___x_3814_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3816_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3817_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3819_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13,
    );
    v___x_3820_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3822_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3823_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3832_: u8 = 0;
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3832_ = 1;
    v___x_3833_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46;
    v___x_3834_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3833_, v___x_3832_);
    return v___x_3834_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48()
-> *mut leanh::LeanObject {
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3835_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47,
    );
    v___x_3836_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3838_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3839_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3848_ = 1;
    v___x_3849_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53;
    v___x_3850_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3849_, v___x_3848_);
    return v___x_3850_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55()
-> *mut leanh::LeanObject {
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3851_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54,
    );
    v___x_3852_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3855_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = 1;
    v___x_3865_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60;
    v___x_3866_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3865_, v___x_3864_);
    return v___x_3866_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62()
-> *mut leanh::LeanObject {
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61,
    );
    v___x_3868_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3871_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3879_: u8 = 0;
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3879_ = 1;
    v___x_3880_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67;
    v___x_3881_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3880_, v___x_3879_);
    return v___x_3881_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69()
-> *mut leanh::LeanObject {
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3882_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once
        ),
        _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68,
    );
    v___x_3883_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_3886_ = leanh::lean_obj_once(
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
    mut v_inst_3888_: *mut leanh::LeanObject,
    mut v_json_3889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3897_: u8 = 0;
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v_a_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3911_: u8 = 0;
    let mut v_a_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_a_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut v_a_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v_a_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3950_: u8 = 0;
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v_a_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut v_a_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut v_a_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3984_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut v_a_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3994_: u8 = 0;
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3998_: u8 = 0;
    let mut v_a_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4006_: u8 = 0;
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut v_a_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v_a_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4033_: u8 = 0;
    let mut v_a_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4037_: u8 = 0;
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4041_: u8 = 0;
    let mut v_a_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut v_a_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_a_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4071_: u8 = 0;
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_a_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut v_a_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4093_: u8 = 0;
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut v_a_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4103_: u8 = 0;
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4107_: u8 = 0;
    let mut v_a_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4115_: u8 = 0;
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4121_: u8 = 0;
    let mut v_a_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4125_: u8 = 0;
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4129_: u8 = 0;
    let mut v_a_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3890_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0;
                v___x_3891_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1;
                v___x_3892_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7;
                leanh::lean_inc(v_json_3889_);
                v___x_3893_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_3890_, v___x_3892_);
                if leanh::lean_obj_tag(v___x_3893_) == 0 {
                    leanh::lean_dec(v_json_3889_);
                    leanh::lean_dec_ref(v_inst_3888_);
                    v_a_3894_ = leanh::lean_ctor_get(v___x_3893_, 0);
                    v_isSharedCheck_3903_ = (!leanh::lean_is_exclusive(v___x_3893_)) as u8;
                    if v_isSharedCheck_3903_ == 0 {
                        v___x_3896_ = v___x_3893_;
                        v_isShared_3897_ = v_isSharedCheck_3903_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3894_);
                        leanh::lean_dec(v___x_3893_);
                        v___x_3896_ = leanh::lean_box(0);
                        v_isShared_3897_ = v_isSharedCheck_3903_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_3893_) == 0 {
                        leanh::lean_dec(v_json_3889_);
                        leanh::lean_dec_ref(v_inst_3888_);
                        v_a_3904_ = leanh::lean_ctor_get(v___x_3893_, 0);
                        v_isSharedCheck_3911_ =
                            (!leanh::lean_is_exclusive(v___x_3893_)) as u8;
                        if v_isSharedCheck_3911_ == 0 {
                            v___x_3906_ = v___x_3893_;
                            v_isShared_3907_ = v_isSharedCheck_3911_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3904_);
                            leanh::lean_dec(v___x_3893_);
                            v___x_3906_ = leanh::lean_box(0);
                            v_isShared_3907_ = v_isSharedCheck_3911_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3912_ = leanh::lean_ctor_get(v___x_3893_, 0);
                        leanh::lean_inc(v_a_3912_);
                        leanh::lean_dec_ref_known(v___x_3893_, 1);
                        v___x_3913_ =
                            l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8;
                        leanh::lean_inc(v_json_3889_);
                        v___x_3914_ = l_Lean_Json_getObjValAs_x3f___redArg(
                            v_json_3889_,
                            v___x_3891_,
                            v___x_3913_,
                        );
                        if leanh::lean_obj_tag(v___x_3914_) == 0 {
                            leanh::lean_dec(v_a_3912_);
                            leanh::lean_dec(v_json_3889_);
                            leanh::lean_dec_ref(v_inst_3888_);
                            v_a_3915_ = leanh::lean_ctor_get(v___x_3914_, 0);
                            v_isSharedCheck_3924_ =
                                (!leanh::lean_is_exclusive(v___x_3914_)) as u8;
                            if v_isSharedCheck_3924_ == 0 {
                                v___x_3917_ = v___x_3914_;
                                v_isShared_3918_ = v_isSharedCheck_3924_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3915_);
                                leanh::lean_dec(v___x_3914_);
                                v___x_3917_ = leanh::lean_box(0);
                                v_isShared_3918_ = v_isSharedCheck_3924_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_3914_) == 0 {
                                leanh::lean_dec(v_a_3912_);
                                leanh::lean_dec(v_json_3889_);
                                leanh::lean_dec_ref(v_inst_3888_);
                                v_a_3925_ = leanh::lean_ctor_get(v___x_3914_, 0);
                                v_isSharedCheck_3932_ =
                                    (!leanh::lean_is_exclusive(v___x_3914_)) as u8;
                                if v_isSharedCheck_3932_ == 0 {
                                    v___x_3927_ = v___x_3914_;
                                    v_isShared_3928_ = v_isSharedCheck_3932_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3925_);
                                    leanh::lean_dec(v___x_3914_);
                                    v___x_3927_ = leanh::lean_box(0);
                                    v_isShared_3928_ = v_isSharedCheck_3932_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3933_ = leanh::lean_ctor_get(v___x_3914_, 0);
                                leanh::lean_inc(v_a_3933_);
                                leanh::lean_dec_ref_known(v___x_3914_, 1);
                                v___x_3934_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15;
                                v___x_3935_ =
                                    l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9;
                                leanh::lean_inc(v_json_3889_);
                                v___x_3936_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                    v_json_3889_,
                                    v___x_3934_,
                                    v___x_3935_,
                                );
                                if leanh::lean_obj_tag(v___x_3936_) == 0 {
                                    leanh::lean_dec(v_a_3933_);
                                    leanh::lean_dec(v_a_3912_);
                                    leanh::lean_dec(v_json_3889_);
                                    leanh::lean_dec_ref(v_inst_3888_);
                                    v_a_3937_ = leanh::lean_ctor_get(v___x_3936_, 0);
                                    v_isSharedCheck_3946_ =
                                        (!leanh::lean_is_exclusive(v___x_3936_)) as u8;
                                    if v_isSharedCheck_3946_ == 0 {
                                        v___x_3939_ = v___x_3936_;
                                        v_isShared_3940_ = v_isSharedCheck_3946_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3937_);
                                        leanh::lean_dec(v___x_3936_);
                                        v___x_3939_ = leanh::lean_box(0);
                                        v_isShared_3940_ = v_isSharedCheck_3946_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_3936_) == 0 {
                                        leanh::lean_dec(v_a_3933_);
                                        leanh::lean_dec(v_a_3912_);
                                        leanh::lean_dec(v_json_3889_);
                                        leanh::lean_dec_ref(v_inst_3888_);
                                        v_a_3947_ = leanh::lean_ctor_get(v___x_3936_, 0);
                                        v_isSharedCheck_3954_ =
                                            (!leanh::lean_is_exclusive(v___x_3936_)) as u8;
                                        if v_isSharedCheck_3954_ == 0 {
                                            v___x_3949_ = v___x_3936_;
                                            v_isShared_3950_ = v_isSharedCheck_3954_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3947_);
                                            leanh::lean_dec(v___x_3936_);
                                            v___x_3949_ = leanh::lean_box(0);
                                            v_isShared_3950_ = v_isSharedCheck_3954_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_3955_ = leanh::lean_ctor_get(v___x_3936_, 0);
                                        leanh::lean_inc(v_a_3955_);
                                        leanh::lean_dec_ref_known(v___x_3936_, 1);
                                        v___x_3956_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22;
                                        v___x_3957_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10;
                                        leanh::lean_inc(v_json_3889_);
                                        v___x_3958_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                            v_json_3889_,
                                            v___x_3956_,
                                            v___x_3957_,
                                        );
                                        if leanh::lean_obj_tag(v___x_3958_) == 0 {
                                            leanh::lean_dec(v_a_3955_);
                                            leanh::lean_dec(v_a_3933_);
                                            leanh::lean_dec(v_a_3912_);
                                            leanh::lean_dec(v_json_3889_);
                                            leanh::lean_dec_ref(v_inst_3888_);
                                            v_a_3959_ = leanh::lean_ctor_get(v___x_3958_, 0);
                                            v_isSharedCheck_3968_ =
                                                (!leanh::lean_is_exclusive(v___x_3958_))
                                                    as u8;
                                            if v_isSharedCheck_3968_ == 0 {
                                                v___x_3961_ = v___x_3958_;
                                                v_isShared_3962_ = v_isSharedCheck_3968_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3959_);
                                                leanh::lean_dec(v___x_3958_);
                                                v___x_3961_ = leanh::lean_box(0);
                                                v_isShared_3962_ = v_isSharedCheck_3968_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_3958_) == 0 {
                                                leanh::lean_dec(v_a_3955_);
                                                leanh::lean_dec(v_a_3933_);
                                                leanh::lean_dec(v_a_3912_);
                                                leanh::lean_dec(v_json_3889_);
                                                leanh::lean_dec_ref(v_inst_3888_);
                                                v_a_3969_ =
                                                    leanh::lean_ctor_get(v___x_3958_, 0);
                                                v_isSharedCheck_3976_ =
                                                    (!leanh::lean_is_exclusive(v___x_3958_))
                                                        as u8;
                                                if v_isSharedCheck_3976_ == 0 {
                                                    v___x_3971_ = v___x_3958_;
                                                    v_isShared_3972_ = v_isSharedCheck_3976_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_3969_);
                                                    leanh::lean_dec(v___x_3958_);
                                                    v___x_3971_ = leanh::lean_box(0);
                                                    v_isShared_3972_ = v_isSharedCheck_3976_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_3977_ =
                                                    leanh::lean_ctor_get(v___x_3958_, 0);
                                                leanh::lean_inc(v_a_3977_);
                                                leanh::lean_dec_ref_known(v___x_3958_, 1);
                                                v___x_3978_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28;
                                                v___x_3979_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11;
                                                leanh::lean_inc(v_json_3889_);
                                                v___x_3980_ = l_Lean_Json_getObjValAs_x3f___redArg(
                                                    v_json_3889_,
                                                    v___x_3978_,
                                                    v___x_3979_,
                                                );
                                                if leanh::lean_obj_tag(v___x_3980_) == 0 {
                                                    leanh::lean_dec(v_a_3977_);
                                                    leanh::lean_dec(v_a_3955_);
                                                    leanh::lean_dec(v_a_3933_);
                                                    leanh::lean_dec(v_a_3912_);
                                                    leanh::lean_dec(v_json_3889_);
                                                    leanh::lean_dec_ref(v_inst_3888_);
                                                    v_a_3981_ =
                                                        leanh::lean_ctor_get(v___x_3980_, 0);
                                                    v_isSharedCheck_3990_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3980_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3990_ == 0 {
                                                        v___x_3983_ = v___x_3980_;
                                                        v_isShared_3984_ = v_isSharedCheck_3990_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3981_);
                                                        leanh::lean_dec(v___x_3980_);
                                                        v___x_3983_ = leanh::lean_box(0);
                                                        v_isShared_3984_ = v_isSharedCheck_3990_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if leanh::lean_obj_tag(v___x_3980_) == 0
                                                    {
                                                        leanh::lean_dec(v_a_3977_);
                                                        leanh::lean_dec(v_a_3955_);
                                                        leanh::lean_dec(v_a_3933_);
                                                        leanh::lean_dec(v_a_3912_);
                                                        leanh::lean_dec(v_json_3889_);
                                                        leanh::lean_dec_ref(v_inst_3888_);
                                                        v_a_3991_ = leanh::lean_ctor_get(
                                                            v___x_3980_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3998_ =
                                                            (!leanh::lean_is_exclusive(
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
                                                            leanh::lean_inc(v_a_3991_);
                                                            leanh::lean_dec(v___x_3980_);
                                                            v___x_3993_ = leanh::lean_box(0);
                                                            v_isShared_3994_ =
                                                                v_isSharedCheck_3998_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_3999_ = leanh::lean_ctor_get(
                                                            v___x_3980_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_3999_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_3980_,
                                                            1,
                                                        );
                                                        v___x_4000_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35;
                                                        v___x_4001_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12;
                                                        leanh::lean_inc(v_json_3889_);
                                                        v___x_4002_ =
                                                            l_Lean_Json_getObjValAs_x3f___redArg(
                                                                v_json_3889_,
                                                                v___x_4000_,
                                                                v___x_4001_,
                                                            );
                                                        if leanh::lean_obj_tag(v___x_4002_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec(v_a_3999_);
                                                            leanh::lean_dec(v_a_3977_);
                                                            leanh::lean_dec(v_a_3955_);
                                                            leanh::lean_dec(v_a_3933_);
                                                            leanh::lean_dec(v_a_3912_);
                                                            leanh::lean_dec(v_json_3889_);
                                                            leanh::lean_dec_ref(
                                                                v_inst_3888_,
                                                            );
                                                            v_a_4003_ = leanh::lean_ctor_get(
                                                                v___x_4002_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4012_ =
                                                                (!leanh::lean_is_exclusive(
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
                                                                leanh::lean_inc(v_a_4003_);
                                                                leanh::lean_dec(v___x_4002_);
                                                                v___x_4005_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_4006_ =
                                                                    v_isSharedCheck_4012_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if leanh::lean_obj_tag(
                                                                v___x_4002_,
                                                            ) == 0
                                                            {
                                                                leanh::lean_dec(v_a_3999_);
                                                                leanh::lean_dec(v_a_3977_);
                                                                leanh::lean_dec(v_a_3955_);
                                                                leanh::lean_dec(v_a_3933_);
                                                                leanh::lean_dec(v_a_3912_);
                                                                leanh::lean_dec(
                                                                    v_json_3889_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_inst_3888_,
                                                                );
                                                                v_a_4013_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_4002_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_4020_ = (!leanh::lean_is_exclusive(v___x_4002_)) as u8;
                                                                if v_isSharedCheck_4020_ == 0 {
                                                                    v___x_4015_ = v___x_4002_;
                                                                    v_isShared_4016_ =
                                                                        v_isSharedCheck_4020_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_4013_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_4002_,
                                                                    );
                                                                    v___x_4015_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_4016_ =
                                                                        v_isSharedCheck_4020_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_4021_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_4002_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_a_4021_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_4002_,
                                                                    1,
                                                                );
                                                                v___x_4022_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
                                                                leanh::lean_inc(
                                                                    v_json_3889_,
                                                                );
                                                                v___x_4023_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v_inst_3888_, v___x_4022_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_4023_,
                                                                ) == 0
                                                                {
                                                                    leanh::lean_dec(
                                                                        v_a_4021_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3999_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3977_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3955_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3933_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3912_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_json_3889_,
                                                                    );
                                                                    v_a_4024_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_4023_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_4033_ = (!leanh::lean_is_exclusive(v___x_4023_)) as u8;
                                                                    if v_isSharedCheck_4033_ == 0 {
                                                                        v___x_4026_ = v___x_4023_;
                                                                        v_isShared_4027_ =
                                                                            v_isSharedCheck_4033_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_4024_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_4023_,
                                                                        );
                                                                        v___x_4026_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_4027_ =
                                                                            v_isSharedCheck_4033_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_4023_,
                                                                    ) == 0
                                                                    {
                                                                        leanh::lean_dec(
                                                                            v_a_4021_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3999_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3977_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3955_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3933_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3912_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_json_3889_,
                                                                        );
                                                                        v_a_4034_ = leanh::lean_ctor_get(v___x_4023_, 0);
                                                                        v_isSharedCheck_4041_ = (!leanh::lean_is_exclusive(v___x_4023_)) as u8;
                                                                        if v_isSharedCheck_4041_
                                                                            == 0
                                                                        {
                                                                            v___x_4036_ =
                                                                                v___x_4023_;
                                                                            v_isShared_4037_ = v_isSharedCheck_4041_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_4034_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_4023_,
                                                                            );
                                                                            v___x_4036_ = leanh::lean_box(0);
                                                                            v_isShared_4037_ = v_isSharedCheck_4041_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_4042_ = leanh::lean_ctor_get(v___x_4023_, 0);
                                                                        leanh::lean_inc(
                                                                            v_a_4042_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v___x_4023_, 1);
                                                                        v___x_4043_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44;
                                                                        v___x_4044_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13;
                                                                        leanh::lean_inc(
                                                                            v_json_3889_,
                                                                        );
                                                                        v___x_4045_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_4043_, v___x_4044_);
                                                                        if leanh::lean_obj_tag(v___x_4045_) == 0 {
leanh::lean_dec(v_a_4042_);
leanh::lean_dec(v_a_4021_);
leanh::lean_dec(v_a_3999_);
leanh::lean_dec(v_a_3977_);
leanh::lean_dec(v_a_3955_);
leanh::lean_dec(v_a_3933_);
leanh::lean_dec(v_a_3912_);
leanh::lean_dec(v_json_3889_);
v_a_4046_ = leanh::lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4055_ = (!leanh::lean_is_exclusive(v___x_4045_)) as u8;
if v_isSharedCheck_4055_ == 0 {
v___x_4048_ = v___x_4045_;
v_isShared_4049_ = v_isSharedCheck_4055_;
state = 29; continue;
} else {
leanh::lean_inc(v_a_4046_);
leanh::lean_dec(v___x_4045_);
v___x_4048_ = leanh::lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4055_;
state = 29; continue;
}
} else {
if leanh::lean_obj_tag(v___x_4045_) == 0 {
leanh::lean_dec(v_a_4042_);
leanh::lean_dec(v_a_4021_);
leanh::lean_dec(v_a_3999_);
leanh::lean_dec(v_a_3977_);
leanh::lean_dec(v_a_3955_);
leanh::lean_dec(v_a_3933_);
leanh::lean_dec(v_a_3912_);
leanh::lean_dec(v_json_3889_);
v_a_4056_ = leanh::lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4063_ = (!leanh::lean_is_exclusive(v___x_4045_)) as u8;
if v_isSharedCheck_4063_ == 0 {
v___x_4058_ = v___x_4045_;
v_isShared_4059_ = v_isSharedCheck_4063_;
state = 31; continue;
} else {
leanh::lean_inc(v_a_4056_);
leanh::lean_dec(v___x_4045_);
v___x_4058_ = leanh::lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
state = 31; continue;
}
} else {
v_a_4064_ = leanh::lean_ctor_get(v___x_4045_, 0);
leanh::lean_inc(v_a_4064_);
leanh::lean_dec_ref_known(v___x_4045_, 1);
v___x_4065_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51;
v___x_4066_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14;
leanh::lean_inc(v_json_3889_);
v___x_4067_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_4065_, v___x_4066_);
if leanh::lean_obj_tag(v___x_4067_) == 0 {
leanh::lean_dec(v_a_4064_);
leanh::lean_dec(v_a_4042_);
leanh::lean_dec(v_a_4021_);
leanh::lean_dec(v_a_3999_);
leanh::lean_dec(v_a_3977_);
leanh::lean_dec(v_a_3955_);
leanh::lean_dec(v_a_3933_);
leanh::lean_dec(v_a_3912_);
leanh::lean_dec(v_json_3889_);
v_a_4068_ = leanh::lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4077_ = (!leanh::lean_is_exclusive(v___x_4067_)) as u8;
if v_isSharedCheck_4077_ == 0 {
v___x_4070_ = v___x_4067_;
v_isShared_4071_ = v_isSharedCheck_4077_;
state = 33; continue;
} else {
leanh::lean_inc(v_a_4068_);
leanh::lean_dec(v___x_4067_);
v___x_4070_ = leanh::lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4077_;
state = 33; continue;
}
} else {
if leanh::lean_obj_tag(v___x_4067_) == 0 {
leanh::lean_dec(v_a_4064_);
leanh::lean_dec(v_a_4042_);
leanh::lean_dec(v_a_4021_);
leanh::lean_dec(v_a_3999_);
leanh::lean_dec(v_a_3977_);
leanh::lean_dec(v_a_3955_);
leanh::lean_dec(v_a_3933_);
leanh::lean_dec(v_a_3912_);
leanh::lean_dec(v_json_3889_);
v_a_4078_ = leanh::lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4085_ = (!leanh::lean_is_exclusive(v___x_4067_)) as u8;
if v_isSharedCheck_4085_ == 0 {
v___x_4080_ = v___x_4067_;
v_isShared_4081_ = v_isSharedCheck_4085_;
state = 35; continue;
} else {
leanh::lean_inc(v_a_4078_);
leanh::lean_dec(v___x_4067_);
v___x_4080_ = leanh::lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
state = 35; continue;
}
} else {
v_a_4086_ = leanh::lean_ctor_get(v___x_4067_, 0);
leanh::lean_inc(v_a_4086_);
leanh::lean_dec_ref_known(v___x_4067_, 1);
v___x_4087_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58;
v___x_4088_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15;
leanh::lean_inc(v_json_3889_);
v___x_4089_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_4087_, v___x_4088_);
if leanh::lean_obj_tag(v___x_4089_) == 0 {
leanh::lean_dec(v_a_4086_);
leanh::lean_dec(v_a_4064_);
leanh::lean_dec(v_a_4042_);
leanh::lean_dec(v_a_4021_);
leanh::lean_dec(v_a_3999_);
leanh::lean_dec(v_a_3977_);
leanh::lean_dec(v_a_3955_);
leanh::lean_dec(v_a_3933_);
leanh::lean_dec(v_a_3912_);
leanh::lean_dec(v_json_3889_);
v_a_4090_ = leanh::lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4099_ = (!leanh::lean_is_exclusive(v___x_4089_)) as u8;
if v_isSharedCheck_4099_ == 0 {
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4099_;
state = 37; continue;
} else {
leanh::lean_inc(v_a_4090_);
leanh::lean_dec(v___x_4089_);
v___x_4092_ = leanh::lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4099_;
state = 37; continue;
}
} else {
if leanh::lean_obj_tag(v___x_4089_) == 0 {
leanh::lean_dec(v_a_4086_);
leanh::lean_dec(v_a_4064_);
leanh::lean_dec(v_a_4042_);
leanh::lean_dec(v_a_4021_);
leanh::lean_dec(v_a_3999_);
leanh::lean_dec(v_a_3977_);
leanh::lean_dec(v_a_3955_);
leanh::lean_dec(v_a_3933_);
leanh::lean_dec(v_a_3912_);
leanh::lean_dec(v_json_3889_);
v_a_4100_ = leanh::lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4107_ = (!leanh::lean_is_exclusive(v___x_4089_)) as u8;
if v_isSharedCheck_4107_ == 0 {
v___x_4102_ = v___x_4089_;
v_isShared_4103_ = v_isSharedCheck_4107_;
state = 39; continue;
} else {
leanh::lean_inc(v_a_4100_);
leanh::lean_dec(v___x_4089_);
v___x_4102_ = leanh::lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
state = 39; continue;
}
} else {
v_a_4108_ = leanh::lean_ctor_get(v___x_4089_, 0);
leanh::lean_inc(v_a_4108_);
leanh::lean_dec_ref_known(v___x_4089_, 1);
v___x_4109_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65;
v___x_4110_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16;
v___x_4111_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_3889_, v___x_4109_, v___x_4110_);
if leanh::lean_obj_tag(v___x_4111_) == 0 {
leanh::lean_dec(v_a_4108_);
leanh::lean_dec(v_a_4086_);
leanh::lean_dec(v_a_4064_);
leanh::lean_dec(v_a_4042_);
leanh::lean_dec(v_a_4021_);
leanh::lean_dec(v_a_3999_);
leanh::lean_dec(v_a_3977_);
leanh::lean_dec(v_a_3955_);
leanh::lean_dec(v_a_3933_);
leanh::lean_dec(v_a_3912_);
v_a_4112_ = leanh::lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4121_ = (!leanh::lean_is_exclusive(v___x_4111_)) as u8;
if v_isSharedCheck_4121_ == 0 {
v___x_4114_ = v___x_4111_;
v_isShared_4115_ = v_isSharedCheck_4121_;
state = 41; continue;
} else {
leanh::lean_inc(v_a_4112_);
leanh::lean_dec(v___x_4111_);
v___x_4114_ = leanh::lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4121_;
state = 41; continue;
}
} else {
if leanh::lean_obj_tag(v___x_4111_) == 0 {
leanh::lean_dec(v_a_4108_);
leanh::lean_dec(v_a_4086_);
leanh::lean_dec(v_a_4064_);
leanh::lean_dec(v_a_4042_);
leanh::lean_dec(v_a_4021_);
leanh::lean_dec(v_a_3999_);
leanh::lean_dec(v_a_3977_);
leanh::lean_dec(v_a_3955_);
leanh::lean_dec(v_a_3933_);
leanh::lean_dec(v_a_3912_);
v_a_4122_ = leanh::lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4129_ = (!leanh::lean_is_exclusive(v___x_4111_)) as u8;
if v_isSharedCheck_4129_ == 0 {
v___x_4124_ = v___x_4111_;
v_isShared_4125_ = v_isSharedCheck_4129_;
state = 43; continue;
} else {
leanh::lean_inc(v_a_4122_);
leanh::lean_dec(v___x_4111_);
v___x_4124_ = leanh::lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
state = 43; continue;
}
} else {
v_a_4130_ = leanh::lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4138_ = (!leanh::lean_is_exclusive(v___x_4111_)) as u8;
if v_isSharedCheck_4138_ == 0 {
v___x_4132_ = v___x_4111_;
v_isShared_4133_ = v_isSharedCheck_4138_;
state = 45; continue;
} else {
leanh::lean_inc(v_a_4130_);
leanh::lean_dec(v___x_4111_);
v___x_4132_ = leanh::lean_box(0);
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
                v___x_3898_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9,
                );
                v___x_3899_ = lean_string_append(v___x_3898_, v_a_3894_);
                leanh::lean_dec(v_a_3894_);
                if v_isShared_3897_ == 0 {
                    leanh::lean_ctor_set(v___x_3896_, 0, v___x_3899_);
                    v___x_3901_ = v___x_3896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3899_);
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
                    leanh::lean_ctor_set_tag(v___x_3906_, 0);
                    v___x_3909_ = v___x_3906_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3910_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
                    v___x_3909_ = v_reuseFailAlloc_3910_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3909_;
            }
            5 => {
                v___x_3919_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14,
                );
                v___x_3920_ = lean_string_append(v___x_3919_, v_a_3915_);
                leanh::lean_dec(v_a_3915_);
                if v_isShared_3918_ == 0 {
                    leanh::lean_ctor_set(v___x_3917_, 0, v___x_3920_);
                    v___x_3922_ = v___x_3917_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
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
                    leanh::lean_ctor_set_tag(v___x_3927_, 0);
                    v___x_3930_ = v___x_3927_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
                    v___x_3930_ = v_reuseFailAlloc_3931_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3930_;
            }
            9 => {
                v___x_3941_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20,
                );
                v___x_3942_ = lean_string_append(v___x_3941_, v_a_3937_);
                leanh::lean_dec(v_a_3937_);
                if v_isShared_3940_ == 0 {
                    leanh::lean_ctor_set(v___x_3939_, 0, v___x_3942_);
                    v___x_3944_ = v___x_3939_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3945_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
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
                    leanh::lean_ctor_set_tag(v___x_3949_, 0);
                    v___x_3952_ = v___x_3949_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
                    v___x_3952_ = v_reuseFailAlloc_3953_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3952_;
            }
            13 => {
                v___x_3963_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27,
                );
                v___x_3964_ = lean_string_append(v___x_3963_, v_a_3959_);
                leanh::lean_dec(v_a_3959_);
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_3964_);
                    v___x_3966_ = v___x_3961_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3964_);
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
                    leanh::lean_ctor_set_tag(v___x_3971_, 0);
                    v___x_3974_ = v___x_3971_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
                    v___x_3974_ = v_reuseFailAlloc_3975_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3974_;
            }
            17 => {
                v___x_3985_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33,
                );
                v___x_3986_ = lean_string_append(v___x_3985_, v_a_3981_);
                leanh::lean_dec(v_a_3981_);
                if v_isShared_3984_ == 0 {
                    leanh::lean_ctor_set(v___x_3983_, 0, v___x_3986_);
                    v___x_3988_ = v___x_3983_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3986_);
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
                    leanh::lean_ctor_set_tag(v___x_3993_, 0);
                    v___x_3996_ = v___x_3993_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
                    v___x_3996_ = v_reuseFailAlloc_3997_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3996_;
            }
            21 => {
                v___x_4007_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40,
                );
                v___x_4008_ = lean_string_append(v___x_4007_, v_a_4003_);
                leanh::lean_dec(v_a_4003_);
                if v_isShared_4006_ == 0 {
                    leanh::lean_ctor_set(v___x_4005_, 0, v___x_4008_);
                    v___x_4010_ = v___x_4005_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4008_);
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
                    leanh::lean_ctor_set_tag(v___x_4015_, 0);
                    v___x_4018_ = v___x_4015_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4018_;
            }
            25 => {
                v___x_4028_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42,
                );
                v___x_4029_ = lean_string_append(v___x_4028_, v_a_4024_);
                leanh::lean_dec(v_a_4024_);
                if v_isShared_4027_ == 0 {
                    leanh::lean_ctor_set(v___x_4026_, 0, v___x_4029_);
                    v___x_4031_ = v___x_4026_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4029_);
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
                    leanh::lean_ctor_set_tag(v___x_4036_, 0);
                    v___x_4039_ = v___x_4036_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4040_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
                    v___x_4039_ = v_reuseFailAlloc_4040_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4039_;
            }
            29 => {
                v___x_4050_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49,
                );
                v___x_4051_ = lean_string_append(v___x_4050_, v_a_4046_);
                leanh::lean_dec(v_a_4046_);
                if v_isShared_4049_ == 0 {
                    leanh::lean_ctor_set(v___x_4048_, 0, v___x_4051_);
                    v___x_4053_ = v___x_4048_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4051_);
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
                    leanh::lean_ctor_set_tag(v___x_4058_, 0);
                    v___x_4061_ = v___x_4058_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
                    v___x_4061_ = v_reuseFailAlloc_4062_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4061_;
            }
            33 => {
                v___x_4072_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56,
                );
                v___x_4073_ = lean_string_append(v___x_4072_, v_a_4068_);
                leanh::lean_dec(v_a_4068_);
                if v_isShared_4071_ == 0 {
                    leanh::lean_ctor_set(v___x_4070_, 0, v___x_4073_);
                    v___x_4075_ = v___x_4070_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
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
                    leanh::lean_ctor_set_tag(v___x_4080_, 0);
                    v___x_4083_ = v___x_4080_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
                    v___x_4083_ = v_reuseFailAlloc_4084_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4083_;
            }
            37 => {
                v___x_4094_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63,
                );
                v___x_4095_ = lean_string_append(v___x_4094_, v_a_4090_);
                leanh::lean_dec(v_a_4090_);
                if v_isShared_4093_ == 0 {
                    leanh::lean_ctor_set(v___x_4092_, 0, v___x_4095_);
                    v___x_4097_ = v___x_4092_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4098_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4095_);
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
                    leanh::lean_ctor_set_tag(v___x_4102_, 0);
                    v___x_4105_ = v___x_4102_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
                    v___x_4105_ = v_reuseFailAlloc_4106_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4105_;
            }
            41 => {
                v___x_4116_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70,
                );
                v___x_4117_ = lean_string_append(v___x_4116_, v_a_4112_);
                leanh::lean_dec(v_a_4112_);
                if v_isShared_4115_ == 0 {
                    leanh::lean_ctor_set(v___x_4114_, 0, v___x_4117_);
                    v___x_4119_ = v___x_4114_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4120_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4117_);
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
                    leanh::lean_ctor_set_tag(v___x_4124_, 0);
                    v___x_4127_ = v___x_4124_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
                    v___x_4127_ = v_reuseFailAlloc_4128_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4127_;
            }
            45 => {
                v___x_4134_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                leanh::lean_ctor_set(v___x_4134_, 0, v_a_3912_);
                leanh::lean_ctor_set(v___x_4134_, 1, v_a_3933_);
                leanh::lean_ctor_set(v___x_4134_, 2, v_a_3955_);
                leanh::lean_ctor_set(v___x_4134_, 3, v_a_3977_);
                leanh::lean_ctor_set(v___x_4134_, 4, v_a_3999_);
                leanh::lean_ctor_set(v___x_4134_, 5, v_a_4021_);
                leanh::lean_ctor_set(v___x_4134_, 6, v_a_4042_);
                leanh::lean_ctor_set(v___x_4134_, 7, v_a_4064_);
                leanh::lean_ctor_set(v___x_4134_, 8, v_a_4086_);
                leanh::lean_ctor_set(v___x_4134_, 9, v_a_4108_);
                leanh::lean_ctor_set(v___x_4134_, 10, v_a_4130_);
                if v_isShared_4133_ == 0 {
                    leanh::lean_ctor_set(v___x_4132_, 0, v___x_4134_);
                    v___x_4136_ = v___x_4132_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4137_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
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
    mut v_00_u03b1_4139_: *mut leanh::LeanObject,
    mut v_inst_4140_: *mut leanh::LeanObject,
    mut v_json_4141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ =
        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(v_inst_4140_, v_json_4141_);
    return v___x_4142_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(
    mut v_inst_4143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4144_ = leanh::lean_alloc_closure(
        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_4144_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4144_, 1, v_inst_4143_);
    return v___x_4144_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticWith(
    mut v_00_u03b1_4145_: *mut leanh::LeanObject,
    mut v_inst_4146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4147_ = leanh::lean_alloc_closure(
        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_4147_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4147_, 1, v_inst_4146_);
    return v___x_4147_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticWith_fullRange___redArg(
    mut v_d_4148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fullRange_x3f_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fullRange_x3f_4149_ = leanh::lean_ctor_get(v_d_4148_, 1);
    if leanh::lean_obj_tag(v_fullRange_x3f_4149_) == 0 {
        let mut v_range_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_range_4150_ = leanh::lean_ctor_get(v_d_4148_, 0);
        leanh::lean_inc_ref(v_range_4150_);
        return v_range_4150_;
    } else {
        let mut v_val_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4151_ = leanh::lean_ctor_get(v_fullRange_x3f_4149_, 0);
        leanh::lean_inc(v_val_4151_);
        return v_val_4151_;
    }
}
pub unsafe fn l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(
    mut v_d_4152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4153_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_4152_);
    leanh::lean_dec_ref(v_d_4152_);
    return v_res_4153_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticWith_fullRange(
    mut v_00_u03b1_4154_: *mut leanh::LeanObject,
    mut v_d_4155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_4155_);
    return v___x_4156_;
}
pub unsafe fn l_Lean_Lsp_DiagnosticWith_fullRange___boxed(
    mut v_00_u03b1_4157_: *mut leanh::LeanObject,
    mut v_d_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_Lean_Lsp_DiagnosticWith_fullRange(v_00_u03b1_4157_, v_d_4158_);
    leanh::lean_dec_ref(v_d_4158_);
    return v_res_4159_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(
    mut v_x_4168_: *mut leanh::LeanObject,
    mut v_x_4169_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4168_) == 0 {
        if leanh::lean_obj_tag(v_x_4169_) == 0 {
            let mut v___x_4170_: u8 = 0;
            v___x_4170_ = 1;
            return v___x_4170_;
        } else {
            let mut v___x_4171_: u8 = 0;
            v___x_4171_ = 0;
            return v___x_4171_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4169_) == 0 {
            let mut v___x_4172_: u8 = 0;
            v___x_4172_ = 0;
            return v___x_4172_;
        } else {
            let mut v_val_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4175_: u8 = 0;
            v_val_4173_ = leanh::lean_ctor_get(v_x_4168_, 0);
            v_val_4174_ = leanh::lean_ctor_get(v_x_4169_, 0);
            v___x_4175_ = lean_int_dec_eq(v_val_4173_, v_val_4174_);
            return v___x_4175_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(
    mut v_x_4176_: *mut leanh::LeanObject,
    mut v_x_4177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4178_: u8 = 0;
    let mut v_r_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4178_ =
        l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(
            v_x_4176_, v_x_4177_,
        );
    leanh::lean_dec(v_x_4177_);
    leanh::lean_dec(v_x_4176_);
    v_r_4179_ = leanh::lean_box((v_res_4178_) as usize);
    return v_r_4179_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(
    mut v_x_4180_: *mut leanh::LeanObject,
    mut v_x_4181_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4180_) == 0 {
        if leanh::lean_obj_tag(v_x_4181_) == 0 {
            let mut v___x_4182_: u8 = 0;
            v___x_4182_ = 1;
            return v___x_4182_;
        } else {
            let mut v___x_4183_: u8 = 0;
            v___x_4183_ = 0;
            return v___x_4183_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4181_) == 0 {
            let mut v___x_4184_: u8 = 0;
            v___x_4184_ = 0;
            return v___x_4184_;
        } else {
            let mut v_val_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4186_: u8 = 0;
            v_val_4185_ = leanh::lean_ctor_get(v_x_4180_, 0);
            v___x_4186_ = (leanh::lean_unbox(v_val_4185_) as u8);
            if v___x_4186_ == 0 {
                let mut v_val_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4188_: u8 = 0;
                v_val_4187_ = leanh::lean_ctor_get(v_x_4181_, 0);
                v___x_4188_ = (leanh::lean_unbox(v_val_4187_) as u8);
                if v___x_4188_ == 0 {
                    let mut v___x_4189_: u8 = 0;
                    v___x_4189_ = 1;
                    return v___x_4189_;
                } else {
                    let mut v___x_4190_: u8 = 0;
                    v___x_4190_ = (leanh::lean_unbox(v_val_4185_) as u8);
                    return v___x_4190_;
                }
            } else {
                let mut v_val_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4192_: u8 = 0;
                v_val_4191_ = leanh::lean_ctor_get(v_x_4181_, 0);
                v___x_4192_ = (leanh::lean_unbox(v_val_4191_) as u8);
                return v___x_4192_;
            }
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(
    mut v_x_4193_: *mut leanh::LeanObject,
    mut v_x_4194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4195_: u8 = 0;
    let mut v_r_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4195_ =
        l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(
            v_x_4193_, v_x_4194_,
        );
    leanh::lean_dec(v_x_4194_);
    leanh::lean_dec(v_x_4193_);
    v_r_4196_ = leanh::lean_box((v_res_4195_) as usize);
    return v_r_4196_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(
    mut v_xs_4197_: *mut leanh::LeanObject,
    mut v_ys_4198_: *mut leanh::LeanObject,
    mut v_x_4199_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4201_: u8 = 0;
    let mut v_one_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4200_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4201_ = lean_nat_dec_eq(v_x_4199_, v_zero_4200_);
                if v_isZero_4201_ == 1 {
                    leanh::lean_dec(v_x_4199_);
                    return v_isZero_4201_;
                } else {
                    v_one_4202_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4203_ = lean_nat_sub(v_x_4199_, v_one_4202_);
                    leanh::lean_dec(v_x_4199_);
                    v___x_4204_ = lean_array_fget_borrowed(v_xs_4197_, v_n_4203_);
                    v___x_4205_ = lean_array_fget_borrowed(v_ys_4198_, v_n_4203_);
                    v___x_4206_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(
                        v___x_4204_,
                        v___x_4205_,
                    );
                    if v___x_4206_ == 0 {
                        leanh::lean_dec(v_n_4203_);
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
    mut v_xs_4208_: *mut leanh::LeanObject,
    mut v_ys_4209_: *mut leanh::LeanObject,
    mut v_x_4210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4211_: u8 = 0;
    let mut v_r_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_4208_, v_ys_4209_, v_x_4210_);
    leanh::lean_dec_ref(v_ys_4209_);
    leanh::lean_dec_ref(v_xs_4208_);
    v_r_4212_ = leanh::lean_box((v_res_4211_) as usize);
    return v_r_4212_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(
    mut v_x_4213_: *mut leanh::LeanObject,
    mut v_x_4214_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4213_) == 0 {
        if leanh::lean_obj_tag(v_x_4214_) == 0 {
            let mut v___x_4215_: u8 = 0;
            v___x_4215_ = 1;
            return v___x_4215_;
        } else {
            let mut v___x_4216_: u8 = 0;
            v___x_4216_ = 0;
            return v___x_4216_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4214_) == 0 {
            let mut v___x_4217_: u8 = 0;
            v___x_4217_ = 0;
            return v___x_4217_;
        } else {
            let mut v_val_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4222_: u8 = 0;
            v_val_4218_ = leanh::lean_ctor_get(v_x_4213_, 0);
            v_val_4219_ = leanh::lean_ctor_get(v_x_4214_, 0);
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
    mut v_x_4224_: *mut leanh::LeanObject,
    mut v_x_4225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4226_: u8 = 0;
    let mut v_r_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4226_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_x_4224_, v_x_4225_);
    leanh::lean_dec(v_x_4225_);
    leanh::lean_dec(v_x_4224_);
    v_r_4227_ = leanh::lean_box((v_res_4226_) as usize);
    return v_r_4227_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(
    mut v_xs_4228_: *mut leanh::LeanObject,
    mut v_ys_4229_: *mut leanh::LeanObject,
    mut v_x_4230_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4232_: u8 = 0;
    let mut v_one_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: u8 = 0;
    let mut v___x_4238_: u8 = 0;
    let mut v___x_4239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4231_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4232_ = lean_nat_dec_eq(v_x_4230_, v_zero_4231_);
                if v_isZero_4232_ == 1 {
                    leanh::lean_dec(v_x_4230_);
                    return v_isZero_4232_;
                } else {
                    v_one_4233_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4234_ = lean_nat_sub(v_x_4230_, v_one_4233_);
                    leanh::lean_dec(v_x_4230_);
                    v___x_4235_ = lean_array_fget_borrowed(v_xs_4228_, v_n_4234_);
                    v___x_4236_ = lean_array_fget_borrowed(v_ys_4229_, v_n_4234_);
                    v___x_4237_ = (leanh::lean_unbox(v___x_4235_) as u8);
                    v___x_4238_ = (leanh::lean_unbox(v___x_4236_) as u8);
                    v___x_4239_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v___x_4237_, v___x_4238_);
                    if v___x_4239_ == 0 {
                        leanh::lean_dec(v_n_4234_);
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
    mut v_xs_4241_: *mut leanh::LeanObject,
    mut v_ys_4242_: *mut leanh::LeanObject,
    mut v_x_4243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4244_: u8 = 0;
    let mut v_r_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4244_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_4241_, v_ys_4242_, v_x_4243_);
    leanh::lean_dec_ref(v_ys_4242_);
    leanh::lean_dec_ref(v_xs_4241_);
    v_r_4245_ = leanh::lean_box((v_res_4244_) as usize);
    return v_r_4245_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(
    mut v_x_4246_: *mut leanh::LeanObject,
    mut v_x_4247_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4246_) == 0 {
        if leanh::lean_obj_tag(v_x_4247_) == 0 {
            let mut v___x_4248_: u8 = 0;
            v___x_4248_ = 1;
            return v___x_4248_;
        } else {
            let mut v___x_4249_: u8 = 0;
            v___x_4249_ = 0;
            return v___x_4249_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4247_) == 0 {
            let mut v___x_4250_: u8 = 0;
            v___x_4250_ = 0;
            return v___x_4250_;
        } else {
            let mut v_val_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4255_: u8 = 0;
            v_val_4251_ = leanh::lean_ctor_get(v_x_4246_, 0);
            v_val_4252_ = leanh::lean_ctor_get(v_x_4247_, 0);
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
    mut v_x_4257_: *mut leanh::LeanObject,
    mut v_x_4258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4259_: u8 = 0;
    let mut v_r_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_x_4257_, v_x_4258_);
    leanh::lean_dec(v_x_4258_);
    leanh::lean_dec(v_x_4257_);
    v_r_4260_ = leanh::lean_box((v_res_4259_) as usize);
    return v_r_4260_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(
    mut v_x_4261_: *mut leanh::LeanObject,
    mut v_x_4262_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4261_) == 0 {
        if leanh::lean_obj_tag(v_x_4262_) == 0 {
            let mut v___x_4263_: u8 = 0;
            v___x_4263_ = 1;
            return v___x_4263_;
        } else {
            let mut v___x_4264_: u8 = 0;
            v___x_4264_ = 0;
            return v___x_4264_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4262_) == 0 {
            let mut v___x_4265_: u8 = 0;
            v___x_4265_ = 0;
            return v___x_4265_;
        } else {
            let mut v_val_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4268_: u8 = 0;
            v_val_4266_ = leanh::lean_ctor_get(v_x_4261_, 0);
            v_val_4267_ = leanh::lean_ctor_get(v_x_4262_, 0);
            v___x_4268_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_val_4266_, v_val_4267_);
            return v___x_4268_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4___boxed(
    mut v_x_4269_: *mut leanh::LeanObject,
    mut v_x_4270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4271_: u8 = 0;
    let mut v_r_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4271_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_x_4269_, v_x_4270_);
    leanh::lean_dec(v_x_4270_);
    leanh::lean_dec(v_x_4269_);
    v_r_4272_ = leanh::lean_box((v_res_4271_) as usize);
    return v_r_4272_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(
    mut v_x_4273_: *mut leanh::LeanObject,
    mut v_x_4274_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4273_) == 0 {
        if leanh::lean_obj_tag(v_x_4274_) == 0 {
            let mut v___x_4275_: u8 = 0;
            v___x_4275_ = 1;
            return v___x_4275_;
        } else {
            let mut v___x_4276_: u8 = 0;
            v___x_4276_ = 0;
            return v___x_4276_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4274_) == 0 {
            let mut v___x_4277_: u8 = 0;
            v___x_4277_ = 0;
            return v___x_4277_;
        } else {
            let mut v_val_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4280_: u8 = 0;
            v_val_4278_ = leanh::lean_ctor_get(v_x_4273_, 0);
            v_val_4279_ = leanh::lean_ctor_get(v_x_4274_, 0);
            v___x_4280_ = l_Lean_Lsp_instBEqRange_beq(v_val_4278_, v_val_4279_);
            return v___x_4280_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2___boxed(
    mut v_x_4281_: *mut leanh::LeanObject,
    mut v_x_4282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4283_: u8 = 0;
    let mut v_r_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4283_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_x_4281_, v_x_4282_);
    leanh::lean_dec(v_x_4282_);
    leanh::lean_dec(v_x_4281_);
    v_r_4284_ = leanh::lean_box((v_res_4283_) as usize);
    return v_r_4284_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(
    mut v_x_4285_: *mut leanh::LeanObject,
    mut v_x_4286_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4285_) == 0 {
        if leanh::lean_obj_tag(v_x_4286_) == 0 {
            let mut v___x_4287_: u8 = 0;
            v___x_4287_ = 1;
            return v___x_4287_;
        } else {
            let mut v___x_4288_: u8 = 0;
            v___x_4288_ = 0;
            return v___x_4288_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4286_) == 0 {
            let mut v___x_4289_: u8 = 0;
            v___x_4289_ = 0;
            return v___x_4289_;
        } else {
            let mut v_val_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4292_: u8 = 0;
            v_val_4290_ = leanh::lean_ctor_get(v_x_4285_, 0);
            v_val_4291_ = leanh::lean_ctor_get(v_x_4286_, 0);
            v___x_4292_ =
                l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_val_4290_, v_val_4291_);
            return v___x_4292_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9___boxed(
    mut v_x_4293_: *mut leanh::LeanObject,
    mut v_x_4294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4295_: u8 = 0;
    let mut v_r_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4295_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_x_4293_, v_x_4294_);
    leanh::lean_dec(v_x_4294_);
    leanh::lean_dec(v_x_4293_);
    v_r_4296_ = leanh::lean_box((v_res_4295_) as usize);
    return v_r_4296_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(
    mut v_x_4297_: *mut leanh::LeanObject,
    mut v_x_4298_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4297_) == 0 {
        if leanh::lean_obj_tag(v_x_4298_) == 0 {
            let mut v___x_4299_: u8 = 0;
            v___x_4299_ = 1;
            return v___x_4299_;
        } else {
            let mut v___x_4300_: u8 = 0;
            v___x_4300_ = 0;
            return v___x_4300_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4298_) == 0 {
            let mut v___x_4301_: u8 = 0;
            v___x_4301_ = 0;
            return v___x_4301_;
        } else {
            let mut v_val_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4304_: u8 = 0;
            v_val_4302_ = leanh::lean_ctor_get(v_x_4297_, 0);
            v_val_4303_ = leanh::lean_ctor_get(v_x_4298_, 0);
            v___x_4304_ = lean_string_dec_eq(v_val_4302_, v_val_4303_);
            return v___x_4304_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5___boxed(
    mut v_x_4305_: *mut leanh::LeanObject,
    mut v_x_4306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4307_: u8 = 0;
    let mut v_r_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4307_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_x_4305_, v_x_4306_);
    leanh::lean_dec(v_x_4306_);
    leanh::lean_dec(v_x_4305_);
    v_r_4308_ = leanh::lean_box((v_res_4307_) as usize);
    return v_r_4308_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(
    mut v_xs_4309_: *mut leanh::LeanObject,
    mut v_ys_4310_: *mut leanh::LeanObject,
    mut v_x_4311_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4313_: u8 = 0;
    let mut v_one_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: u8 = 0;
    let mut v___x_4319_: u8 = 0;
    let mut v___x_4320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4312_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4313_ = lean_nat_dec_eq(v_x_4311_, v_zero_4312_);
                if v_isZero_4313_ == 1 {
                    leanh::lean_dec(v_x_4311_);
                    return v_isZero_4313_;
                } else {
                    v_one_4314_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4315_ = lean_nat_sub(v_x_4311_, v_one_4314_);
                    leanh::lean_dec(v_x_4311_);
                    v___x_4316_ = lean_array_fget_borrowed(v_xs_4309_, v_n_4315_);
                    v___x_4317_ = lean_array_fget_borrowed(v_ys_4310_, v_n_4315_);
                    v___x_4318_ = (leanh::lean_unbox(v___x_4316_) as u8);
                    v___x_4319_ = (leanh::lean_unbox(v___x_4317_) as u8);
                    v___x_4320_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v___x_4318_, v___x_4319_);
                    if v___x_4320_ == 0 {
                        leanh::lean_dec(v_n_4315_);
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
    mut v_xs_4322_: *mut leanh::LeanObject,
    mut v_ys_4323_: *mut leanh::LeanObject,
    mut v_x_4324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4325_: u8 = 0;
    let mut v_r_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4325_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_4322_, v_ys_4323_, v_x_4324_);
    leanh::lean_dec_ref(v_ys_4323_);
    leanh::lean_dec_ref(v_xs_4322_);
    v_r_4326_ = leanh::lean_box((v_res_4325_) as usize);
    return v_r_4326_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(
    mut v_x_4327_: *mut leanh::LeanObject,
    mut v_x_4328_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4327_) == 0 {
        if leanh::lean_obj_tag(v_x_4328_) == 0 {
            let mut v___x_4329_: u8 = 0;
            v___x_4329_ = 1;
            return v___x_4329_;
        } else {
            let mut v___x_4330_: u8 = 0;
            v___x_4330_ = 0;
            return v___x_4330_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4328_) == 0 {
            let mut v___x_4331_: u8 = 0;
            v___x_4331_ = 0;
            return v___x_4331_;
        } else {
            let mut v_val_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4336_: u8 = 0;
            v_val_4332_ = leanh::lean_ctor_get(v_x_4327_, 0);
            v_val_4333_ = leanh::lean_ctor_get(v_x_4328_, 0);
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
    mut v_x_4338_: *mut leanh::LeanObject,
    mut v_x_4339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4340_: u8 = 0;
    let mut v_r_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_x_4338_, v_x_4339_);
    leanh::lean_dec(v_x_4339_);
    leanh::lean_dec(v_x_4338_);
    v_r_4341_ = leanh::lean_box((v_res_4340_) as usize);
    return v_r_4341_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(
    mut v_x_4342_: *mut leanh::LeanObject,
    mut v_x_4343_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4342_) == 0 {
        if leanh::lean_obj_tag(v_x_4343_) == 0 {
            let mut v___x_4344_: u8 = 0;
            v___x_4344_ = 1;
            return v___x_4344_;
        } else {
            let mut v___x_4345_: u8 = 0;
            v___x_4345_ = 0;
            return v___x_4345_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_4343_) == 0 {
            let mut v___x_4346_: u8 = 0;
            v___x_4346_ = 0;
            return v___x_4346_;
        } else {
            let mut v_val_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4349_: u8 = 0;
            let mut v___x_4350_: u8 = 0;
            let mut v___x_4351_: u8 = 0;
            v_val_4347_ = leanh::lean_ctor_get(v_x_4342_, 0);
            v_val_4348_ = leanh::lean_ctor_get(v_x_4343_, 0);
            v___x_4349_ = (leanh::lean_unbox(v_val_4347_) as u8);
            v___x_4350_ = (leanh::lean_unbox(v_val_4348_) as u8);
            v___x_4351_ = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v___x_4349_, v___x_4350_);
            return v___x_4351_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3___boxed(
    mut v_x_4352_: *mut leanh::LeanObject,
    mut v_x_4353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4354_: u8 = 0;
    let mut v_r_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4354_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_x_4352_, v_x_4353_);
    leanh::lean_dec(v_x_4353_);
    leanh::lean_dec(v_x_4352_);
    v_r_4355_ = leanh::lean_box((v_res_4354_) as usize);
    return v_r_4355_;
}
pub unsafe fn l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(
    mut v_x_4356_: *mut leanh::LeanObject,
    mut v_x_4357_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_range_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    v_range_4358_ = leanh::lean_ctor_get(v_x_4356_, 0);
    v_fullRange_x3f_4359_ = leanh::lean_ctor_get(v_x_4356_, 1);
    v_severity_x3f_4360_ = leanh::lean_ctor_get(v_x_4356_, 2);
    v_isSilent_x3f_4361_ = leanh::lean_ctor_get(v_x_4356_, 3);
    v_code_x3f_4362_ = leanh::lean_ctor_get(v_x_4356_, 4);
    v_source_x3f_4363_ = leanh::lean_ctor_get(v_x_4356_, 5);
    v_message_4364_ = leanh::lean_ctor_get(v_x_4356_, 6);
    v_tags_x3f_4365_ = leanh::lean_ctor_get(v_x_4356_, 7);
    v_leanTags_x3f_4366_ = leanh::lean_ctor_get(v_x_4356_, 8);
    v_relatedInformation_x3f_4367_ = leanh::lean_ctor_get(v_x_4356_, 9);
    v_data_x3f_4368_ = leanh::lean_ctor_get(v_x_4356_, 10);
    v_range_4369_ = leanh::lean_ctor_get(v_x_4357_, 0);
    v_fullRange_x3f_4370_ = leanh::lean_ctor_get(v_x_4357_, 1);
    v_severity_x3f_4371_ = leanh::lean_ctor_get(v_x_4357_, 2);
    v_isSilent_x3f_4372_ = leanh::lean_ctor_get(v_x_4357_, 3);
    v_code_x3f_4373_ = leanh::lean_ctor_get(v_x_4357_, 4);
    v_source_x3f_4374_ = leanh::lean_ctor_get(v_x_4357_, 5);
    v_message_4375_ = leanh::lean_ctor_get(v_x_4357_, 6);
    v_tags_x3f_4376_ = leanh::lean_ctor_get(v_x_4357_, 7);
    v_leanTags_x3f_4377_ = leanh::lean_ctor_get(v_x_4357_, 8);
    v_relatedInformation_x3f_4378_ = leanh::lean_ctor_get(v_x_4357_, 9);
    v_data_x3f_4379_ = leanh::lean_ctor_get(v_x_4357_, 10);
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
    mut v_x_4391_: *mut leanh::LeanObject,
    mut v_x_4392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4393_: u8 = 0;
    let mut v_r_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4393_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v_x_4391_, v_x_4392_);
    leanh::lean_dec_ref(v_x_4392_);
    leanh::lean_dec_ref(v_x_4391_);
    v_r_4394_ = leanh::lean_box((v_res_4393_) as usize);
    return v_r_4394_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(
    mut v_xs_4395_: *mut leanh::LeanObject,
    mut v_ys_4396_: *mut leanh::LeanObject,
    mut v_x_4397_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4399_: u8 = 0;
    let mut v_one_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4398_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4399_ = lean_nat_dec_eq(v_x_4397_, v_zero_4398_);
                if v_isZero_4399_ == 1 {
                    leanh::lean_dec(v_x_4397_);
                    return v_isZero_4399_;
                } else {
                    v_one_4400_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4401_ = lean_nat_sub(v_x_4397_, v_one_4400_);
                    leanh::lean_dec(v_x_4397_);
                    v___x_4402_ = lean_array_fget_borrowed(v_xs_4395_, v_n_4401_);
                    v___x_4403_ = lean_array_fget_borrowed(v_ys_4396_, v_n_4401_);
                    v___x_4404_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v___x_4402_, v___x_4403_);
                    if v___x_4404_ == 0 {
                        leanh::lean_dec(v_n_4401_);
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
    mut v_xs_4406_: *mut leanh::LeanObject,
    mut v_ys_4407_: *mut leanh::LeanObject,
    mut v_x_4408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4409_: u8 = 0;
    let mut v_r_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4409_ =
        l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(
            v_xs_4406_, v_ys_4407_, v_x_4408_,
        );
    leanh::lean_dec_ref(v_ys_4407_);
    leanh::lean_dec_ref(v_xs_4406_);
    v_r_4410_ = leanh::lean_box((v_res_4409_) as usize);
    return v_r_4410_;
}
pub unsafe fn l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(
    mut v_x_4411_: *mut leanh::LeanObject,
    mut v_x_4412_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_uri_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isIncremental_x3f_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isIncremental_x3f_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    v_uri_4413_ = leanh::lean_ctor_get(v_x_4411_, 0);
    v_version_x3f_4414_ = leanh::lean_ctor_get(v_x_4411_, 1);
    v_isIncremental_x3f_4415_ = leanh::lean_ctor_get(v_x_4411_, 2);
    v_diagnostics_4416_ = leanh::lean_ctor_get(v_x_4411_, 3);
    v_uri_4417_ = leanh::lean_ctor_get(v_x_4412_, 0);
    v_version_x3f_4418_ = leanh::lean_ctor_get(v_x_4412_, 1);
    v_isIncremental_x3f_4419_ = leanh::lean_ctor_get(v_x_4412_, 2);
    v_diagnostics_4420_ = leanh::lean_ctor_get(v_x_4412_, 3);
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
                let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_4428_: *mut leanh::LeanObject,
    mut v_x_4429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4430_: u8 = 0;
    let mut v_r_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4430_ = l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(v_x_4428_, v_x_4429_);
    leanh::lean_dec_ref(v_x_4429_);
    leanh::lean_dec_ref(v_x_4428_);
    v_r_4431_ = leanh::lean_box((v_res_4430_) as usize);
    return v_r_4431_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(
    mut v_xs_4432_: *mut leanh::LeanObject,
    mut v_ys_4433_: *mut leanh::LeanObject,
    mut v_hsz_4434_: *mut leanh::LeanObject,
    mut v_x_4435_: *mut leanh::LeanObject,
    mut v_x_4436_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4437_: u8 = 0;
    v___x_4437_ =
        l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(
            v_xs_4432_, v_ys_4433_, v_x_4435_,
        );
    return v___x_4437_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___boxed(
    mut v_xs_4438_: *mut leanh::LeanObject,
    mut v_ys_4439_: *mut leanh::LeanObject,
    mut v_hsz_4440_: *mut leanh::LeanObject,
    mut v_x_4441_: *mut leanh::LeanObject,
    mut v_x_4442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4443_: u8 = 0;
    let mut v_r_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4443_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(
        v_xs_4438_,
        v_ys_4439_,
        v_hsz_4440_,
        v_x_4441_,
        v_x_4442_,
    );
    leanh::lean_dec_ref(v_ys_4439_);
    leanh::lean_dec_ref(v_xs_4438_);
    v_r_4444_ = leanh::lean_box((v_res_4443_) as usize);
    return v_r_4444_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(
    mut v_xs_4445_: *mut leanh::LeanObject,
    mut v_ys_4446_: *mut leanh::LeanObject,
    mut v_hsz_4447_: *mut leanh::LeanObject,
    mut v_x_4448_: *mut leanh::LeanObject,
    mut v_x_4449_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4450_: u8 = 0;
    v___x_4450_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_4445_, v_ys_4446_, v_x_4448_);
    return v___x_4450_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___boxed(
    mut v_xs_4451_: *mut leanh::LeanObject,
    mut v_ys_4452_: *mut leanh::LeanObject,
    mut v_hsz_4453_: *mut leanh::LeanObject,
    mut v_x_4454_: *mut leanh::LeanObject,
    mut v_x_4455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4456_: u8 = 0;
    let mut v_r_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4456_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(v_xs_4451_, v_ys_4452_, v_hsz_4453_, v_x_4454_, v_x_4455_);
    leanh::lean_dec_ref(v_ys_4452_);
    leanh::lean_dec_ref(v_xs_4451_);
    v_r_4457_ = leanh::lean_box((v_res_4456_) as usize);
    return v_r_4457_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(
    mut v_xs_4458_: *mut leanh::LeanObject,
    mut v_ys_4459_: *mut leanh::LeanObject,
    mut v_hsz_4460_: *mut leanh::LeanObject,
    mut v_x_4461_: *mut leanh::LeanObject,
    mut v_x_4462_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4463_: u8 = 0;
    v___x_4463_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_4458_, v_ys_4459_, v_x_4461_);
    return v___x_4463_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___boxed(
    mut v_xs_4464_: *mut leanh::LeanObject,
    mut v_ys_4465_: *mut leanh::LeanObject,
    mut v_hsz_4466_: *mut leanh::LeanObject,
    mut v_x_4467_: *mut leanh::LeanObject,
    mut v_x_4468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4469_: u8 = 0;
    let mut v_r_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4469_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(v_xs_4464_, v_ys_4465_, v_hsz_4466_, v_x_4467_, v_x_4468_);
    leanh::lean_dec_ref(v_ys_4465_);
    leanh::lean_dec_ref(v_xs_4464_);
    v_r_4470_ = leanh::lean_box((v_res_4469_) as usize);
    return v_r_4470_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(
    mut v_xs_4471_: *mut leanh::LeanObject,
    mut v_ys_4472_: *mut leanh::LeanObject,
    mut v_hsz_4473_: *mut leanh::LeanObject,
    mut v_x_4474_: *mut leanh::LeanObject,
    mut v_x_4475_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4476_: u8 = 0;
    v___x_4476_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_4471_, v_ys_4472_, v_x_4474_);
    return v___x_4476_;
}
pub unsafe fn l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___boxed(
    mut v_xs_4477_: *mut leanh::LeanObject,
    mut v_ys_4478_: *mut leanh::LeanObject,
    mut v_hsz_4479_: *mut leanh::LeanObject,
    mut v_x_4480_: *mut leanh::LeanObject,
    mut v_x_4481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4482_: u8 = 0;
    let mut v_r_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4482_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(v_xs_4477_, v_ys_4478_, v_hsz_4479_, v_x_4480_, v_x_4481_);
    leanh::lean_dec_ref(v_ys_4478_);
    leanh::lean_dec_ref(v_xs_4477_);
    v_r_4483_ = leanh::lean_box((v_res_4482_) as usize);
    return v_r_4483_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(
    mut v_k_4486_: *mut leanh::LeanObject,
    mut v_x_4487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4492_: u8 = 0;
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4487_) == 0 {
                    leanh::lean_dec_ref(v_k_4486_);
                    v___x_4488_ = leanh::lean_box(0);
                    return v___x_4488_;
                } else {
                    v_val_4489_ = leanh::lean_ctor_get(v_x_4487_, 0);
                    v_isSharedCheck_4500_ = (!leanh::lean_is_exclusive(v_x_4487_)) as u8;
                    if v_isSharedCheck_4500_ == 0 {
                        v___x_4491_ = v_x_4487_;
                        v_isShared_4492_ = v_isSharedCheck_4500_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4489_);
                        leanh::lean_dec(v_x_4487_);
                        v___x_4491_ = leanh::lean_box(0);
                        v_isShared_4492_ = v_isSharedCheck_4500_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4493_ = l_Lean_JsonNumber_fromInt(v_val_4489_);
                if v_isShared_4492_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4491_, 2);
                    leanh::lean_ctor_set(v___x_4491_, 0, v___x_4493_);
                    v___x_4495_ = v___x_4491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4499_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4493_);
                    v___x_4495_ = v_reuseFailAlloc_4499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4496_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4496_, 0, v_k_4486_);
                leanh::lean_ctor_set(v___x_4496_, 1, v___x_4495_);
                v___x_4497_ = leanh::lean_box(0);
                v___x_4498_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4498_, 0, v___x_4496_);
                leanh::lean_ctor_set(v___x_4498_, 1, v___x_4497_);
                return v___x_4498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(
    mut v_k_4501_: *mut leanh::LeanObject,
    mut v_x_4502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4502_) == 0 {
        let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4501_);
        v___x_4503_ = leanh::lean_box(0);
        return v___x_4503_;
    } else {
        let mut v_val_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4506_: u8 = 0;
        let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4504_ = leanh::lean_ctor_get(v_x_4502_, 0);
        v___x_4505_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
        v___x_4506_ = (leanh::lean_unbox(v_val_4504_) as u8);
        leanh::lean_ctor_set_uint8(v___x_4505_, 0 as u32, v___x_4506_);
        v___x_4507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4507_, 0, v_k_4501_);
        leanh::lean_ctor_set(v___x_4507_, 1, v___x_4505_);
        v___x_4508_ = leanh::lean_box(0);
        v___x_4509_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4509_, 0, v___x_4507_);
        leanh::lean_ctor_set(v___x_4509_, 1, v___x_4508_);
        return v___x_4509_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1___boxed(
    mut v_k_4510_: *mut leanh::LeanObject,
    mut v_x_4511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4512_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(
            v_k_4510_, v_x_4511_,
        );
    leanh::lean_dec(v_x_4511_);
    return v_res_4512_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(
    mut v_k_4513_: *mut leanh::LeanObject,
    mut v_x_4514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4514_) == 0 {
        let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4513_);
        v___x_4515_ = leanh::lean_box(0);
        return v___x_4515_;
    } else {
        let mut v_val_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4516_ = leanh::lean_ctor_get(v_x_4514_, 0);
        leanh::lean_inc(v_val_4516_);
        v___x_4517_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4517_, 0, v_k_4513_);
        leanh::lean_ctor_set(v___x_4517_, 1, v_val_4516_);
        v___x_4518_ = leanh::lean_box(0);
        v___x_4519_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4519_, 0, v___x_4517_);
        leanh::lean_ctor_set(v___x_4519_, 1, v___x_4518_);
        return v___x_4519_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10___boxed(
    mut v_k_4520_: *mut leanh::LeanObject,
    mut v_x_4521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4522_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v_k_4520_, v_x_4521_);
    leanh::lean_dec(v_x_4521_);
    return v_res_4522_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(
    mut v_k_4523_: *mut leanh::LeanObject,
    mut v_x_4524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_s_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4544_: u8 = 0;
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4524_) == 0 {
                    leanh::lean_dec_ref(v_k_4523_);
                    v___x_4530_ = leanh::lean_box(0);
                    return v___x_4530_;
                } else {
                    v_val_4531_ = leanh::lean_ctor_get(v_x_4524_, 0);
                    leanh::lean_inc(v_val_4531_);
                    leanh::lean_dec_ref_known(v_x_4524_, 1);
                    if leanh::lean_obj_tag(v_val_4531_) == 0 {
                        v_i_4532_ = leanh::lean_ctor_get(v_val_4531_, 0);
                        v_isSharedCheck_4540_ =
                            (!leanh::lean_is_exclusive(v_val_4531_)) as u8;
                        if v_isSharedCheck_4540_ == 0 {
                            v___x_4534_ = v_val_4531_;
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_i_4532_);
                            leanh::lean_dec(v_val_4531_);
                            v___x_4534_ = leanh::lean_box(0);
                            v_isShared_4535_ = v_isSharedCheck_4540_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_s_4541_ = leanh::lean_ctor_get(v_val_4531_, 0);
                        v_isSharedCheck_4548_ =
                            (!leanh::lean_is_exclusive(v_val_4531_)) as u8;
                        if v_isSharedCheck_4548_ == 0 {
                            v___x_4543_ = v_val_4531_;
                            v_isShared_4544_ = v_isSharedCheck_4548_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_s_4541_);
                            leanh::lean_dec(v_val_4531_);
                            v___x_4543_ = leanh::lean_box(0);
                            v_isShared_4544_ = v_isSharedCheck_4548_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4527_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4527_, 0, v_k_4523_);
                leanh::lean_ctor_set(v___x_4527_, 1, v___y_4526_);
                v___x_4528_ = leanh::lean_box(0);
                v___x_4529_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4529_, 0, v___x_4527_);
                leanh::lean_ctor_set(v___x_4529_, 1, v___x_4528_);
                return v___x_4529_;
            }
            2 => {
                v___x_4536_ = l_Lean_JsonNumber_fromInt(v_i_4532_);
                if v_isShared_4535_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4534_, 2);
                    leanh::lean_ctor_set(v___x_4534_, 0, v___x_4536_);
                    v___x_4538_ = v___x_4534_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4539_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
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
                    leanh::lean_ctor_set_tag(v___x_4543_, 3);
                    v___x_4546_ = v___x_4543_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4547_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_s_4541_);
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
    mut v_k_4549_: *mut leanh::LeanObject,
    mut v_x_4550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4550_) == 0 {
                    leanh::lean_dec_ref(v_k_4549_);
                    v___x_4551_ = leanh::lean_box(0);
                    return v___x_4551_;
                } else {
                    v_val_4552_ = leanh::lean_ctor_get(v_x_4550_, 0);
                    v_isSharedCheck_4562_ = (!leanh::lean_is_exclusive(v_x_4550_)) as u8;
                    if v_isSharedCheck_4562_ == 0 {
                        v___x_4554_ = v_x_4550_;
                        v_isShared_4555_ = v_isSharedCheck_4562_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4552_);
                        leanh::lean_dec(v_x_4550_);
                        v___x_4554_ = leanh::lean_box(0);
                        v_isShared_4555_ = v_isSharedCheck_4562_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4555_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4554_, 3);
                    v___x_4557_ = v___x_4554_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4561_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_val_4552_);
                    v___x_4557_ = v_reuseFailAlloc_4561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4558_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4558_, 0, v_k_4549_);
                leanh::lean_ctor_set(v___x_4558_, 1, v___x_4557_);
                v___x_4559_ = leanh::lean_box(0);
                v___x_4560_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4560_, 0, v___x_4558_);
                leanh::lean_ctor_set(v___x_4560_, 1, v___x_4559_);
                return v___x_4560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(
    mut v_sz_4563_: usize,
    mut v_i_4564_: usize,
    mut v_bs_4565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4566_: u8 = 0;
    let mut v_v_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: usize = 0;
    let mut v___x_4573_: usize = 0;
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4566_ = lean_usize_dec_lt(v_i_4564_, v_sz_4563_);
                if v___x_4566_ == 0 {
                    return v_bs_4565_;
                } else {
                    v_v_4567_ = lean_array_uget(v_bs_4565_, v_i_4564_);
                    v___x_4568_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4569_ = lean_array_uset(v_bs_4565_, v_i_4564_, v___x_4568_);
                    v___x_4576_ = (leanh::lean_unbox(v_v_4567_) as u8);
                    leanh::lean_dec(v_v_4567_);
                    if v___x_4576_ == 0 {
                        v___x_4577_ = leanh::lean_obj_once(
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
                        v___x_4578_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_4571_);
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
    mut v_sz_4579_: *mut leanh::LeanObject,
    mut v_i_4580_: *mut leanh::LeanObject,
    mut v_bs_4581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4582_: usize = 0;
    let mut v_i_boxed_4583_: usize = 0;
    let mut v_res_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4582_ = leanh::lean_unbox_usize(v_sz_4579_);
    leanh::lean_dec(v_sz_4579_);
    v_i_boxed_4583_ = leanh::lean_unbox_usize(v_i_4580_);
    leanh::lean_dec(v_i_4580_);
    v_res_4584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_boxed_4582_, v_i_boxed_4583_, v_bs_4581_);
    return v_res_4584_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(
    mut v_a_4585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4586_: usize = 0;
    let mut v___x_4587_: usize = 0;
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4586_ = lean_array_size(v_a_4585_);
    v___x_4587_ = 0usize;
    v___x_4588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_4586_, v___x_4587_, v_a_4585_);
    v___x_4589_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4589_, 0, v___x_4588_);
    return v___x_4589_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(
    mut v_k_4590_: *mut leanh::LeanObject,
    mut v_x_4591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4591_) == 0 {
        let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4590_);
        v___x_4592_ = leanh::lean_box(0);
        return v___x_4592_;
    } else {
        let mut v_val_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4593_ = leanh::lean_ctor_get(v_x_4591_, 0);
        leanh::lean_inc(v_val_4593_);
        leanh::lean_dec_ref_known(v_x_4591_, 1);
        v___x_4594_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(v_val_4593_);
        v___x_4595_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4595_, 0, v_k_4590_);
        leanh::lean_ctor_set(v___x_4595_, 1, v___x_4594_);
        v___x_4596_ = leanh::lean_box(0);
        v___x_4597_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4597_, 0, v___x_4595_);
        leanh::lean_ctor_set(v___x_4597_, 1, v___x_4596_);
        return v___x_4597_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(
    mut v_k_4598_: *mut leanh::LeanObject,
    mut v_x_4599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: u8 = 0;
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4599_) == 0 {
                    leanh::lean_dec_ref(v_k_4598_);
                    v___x_4605_ = leanh::lean_box(0);
                    return v___x_4605_;
                } else {
                    v_val_4606_ = leanh::lean_ctor_get(v_x_4599_, 0);
                    v___x_4607_ = (leanh::lean_unbox(v_val_4606_) as u8);
                    match v___x_4607_ {
                        0 => {
                            v___x_4608_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once), _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
                            v___y_4601_ = v___x_4608_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_4609_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once), _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
                            v___y_4601_ = v___x_4609_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v___x_4610_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once), _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
                            v___y_4601_ = v___x_4610_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___x_4611_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once), _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
                            v___y_4601_ = v___x_4611_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_4601_);
                v___x_4602_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4602_, 0, v_k_4598_);
                leanh::lean_ctor_set(v___x_4602_, 1, v___y_4601_);
                v___x_4603_ = leanh::lean_box(0);
                v___x_4604_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4604_, 0, v___x_4602_);
                leanh::lean_ctor_set(v___x_4604_, 1, v___x_4603_);
                return v___x_4604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4___boxed(
    mut v_k_4612_: *mut leanh::LeanObject,
    mut v_x_4613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4614_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v_k_4612_, v_x_4613_);
    leanh::lean_dec(v_x_4613_);
    return v_res_4614_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(
    mut v_sz_4615_: usize,
    mut v_i_4616_: usize,
    mut v_bs_4617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4618_: u8 = 0;
    let mut v_v_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: usize = 0;
    let mut v___x_4624_: usize = 0;
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4618_ = lean_usize_dec_lt(v_i_4616_, v_sz_4615_);
                if v___x_4618_ == 0 {
                    return v_bs_4617_;
                } else {
                    v_v_4619_ = lean_array_uget(v_bs_4617_, v_i_4616_);
                    v___x_4620_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_4627_: *mut leanh::LeanObject,
    mut v_i_4628_: *mut leanh::LeanObject,
    mut v_bs_4629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4630_: usize = 0;
    let mut v_i_boxed_4631_: usize = 0;
    let mut v_res_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4630_ = leanh::lean_unbox_usize(v_sz_4627_);
    leanh::lean_dec(v_sz_4627_);
    v_i_boxed_4631_ = leanh::lean_unbox_usize(v_i_4628_);
    leanh::lean_dec(v_i_4628_);
    v_res_4632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_boxed_4630_, v_i_boxed_4631_, v_bs_4629_);
    return v_res_4632_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(
    mut v_a_4633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4634_: usize = 0;
    let mut v___x_4635_: usize = 0;
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4634_ = lean_array_size(v_a_4633_);
    v___x_4635_ = 0usize;
    v___x_4636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_4634_, v___x_4635_, v_a_4633_);
    v___x_4637_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4637_, 0, v___x_4636_);
    return v___x_4637_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(
    mut v_k_4638_: *mut leanh::LeanObject,
    mut v_x_4639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4639_) == 0 {
        let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4638_);
        v___x_4640_ = leanh::lean_box(0);
        return v___x_4640_;
    } else {
        let mut v_val_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4641_ = leanh::lean_ctor_get(v_x_4639_, 0);
        leanh::lean_inc(v_val_4641_);
        leanh::lean_dec_ref_known(v_x_4639_, 1);
        v___x_4642_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(v_val_4641_);
        v___x_4643_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4643_, 0, v_k_4638_);
        leanh::lean_ctor_set(v___x_4643_, 1, v___x_4642_);
        v___x_4644_ = leanh::lean_box(0);
        v___x_4645_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4645_, 0, v___x_4643_);
        leanh::lean_ctor_set(v___x_4645_, 1, v___x_4644_);
        return v___x_4645_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(
    mut v_sz_4646_: usize,
    mut v_i_4647_: usize,
    mut v_bs_4648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4649_: u8 = 0;
    let mut v_v_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: usize = 0;
    let mut v___x_4656_: usize = 0;
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: u8 = 0;
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4649_ = lean_usize_dec_lt(v_i_4647_, v_sz_4646_);
                if v___x_4649_ == 0 {
                    return v_bs_4648_;
                } else {
                    v_v_4650_ = lean_array_uget(v_bs_4648_, v_i_4647_);
                    v___x_4651_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4652_ = lean_array_uset(v_bs_4648_, v_i_4647_, v___x_4651_);
                    v___x_4659_ = (leanh::lean_unbox(v_v_4650_) as u8);
                    leanh::lean_dec(v_v_4650_);
                    if v___x_4659_ == 0 {
                        v___x_4660_ = leanh::lean_obj_once(
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
                        v___x_4661_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_4654_);
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
    mut v_sz_4662_: *mut leanh::LeanObject,
    mut v_i_4663_: *mut leanh::LeanObject,
    mut v_bs_4664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4665_: usize = 0;
    let mut v_i_boxed_4666_: usize = 0;
    let mut v_res_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4665_ = leanh::lean_unbox_usize(v_sz_4662_);
    leanh::lean_dec(v_sz_4662_);
    v_i_boxed_4666_ = leanh::lean_unbox_usize(v_i_4663_);
    leanh::lean_dec(v_i_4663_);
    v_res_4667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_boxed_4665_, v_i_boxed_4666_, v_bs_4664_);
    return v_res_4667_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(
    mut v_a_4668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4669_: usize = 0;
    let mut v___x_4670_: usize = 0;
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4669_ = lean_array_size(v_a_4668_);
    v___x_4670_ = 0usize;
    v___x_4671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_4669_, v___x_4670_, v_a_4668_);
    v___x_4672_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4672_, 0, v___x_4671_);
    return v___x_4672_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(
    mut v_k_4673_: *mut leanh::LeanObject,
    mut v_x_4674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4674_) == 0 {
        let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4673_);
        v___x_4675_ = leanh::lean_box(0);
        return v___x_4675_;
    } else {
        let mut v_val_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4676_ = leanh::lean_ctor_get(v_x_4674_, 0);
        leanh::lean_inc(v_val_4676_);
        leanh::lean_dec_ref_known(v_x_4674_, 1);
        v___x_4677_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(v_val_4676_);
        v___x_4678_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4678_, 0, v_k_4673_);
        leanh::lean_ctor_set(v___x_4678_, 1, v___x_4677_);
        v___x_4679_ = leanh::lean_box(0);
        v___x_4680_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4680_, 0, v___x_4678_);
        leanh::lean_ctor_set(v___x_4680_, 1, v___x_4679_);
        return v___x_4680_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(
    mut v_k_4681_: *mut leanh::LeanObject,
    mut v_x_4682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4682_) == 0 {
        let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4681_);
        v___x_4683_ = leanh::lean_box(0);
        return v___x_4683_;
    } else {
        let mut v_val_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4684_ = leanh::lean_ctor_get(v_x_4682_, 0);
        leanh::lean_inc(v_val_4684_);
        leanh::lean_dec_ref_known(v_x_4682_, 1);
        v___x_4685_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_4684_);
        v___x_4686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4686_, 0, v_k_4681_);
        leanh::lean_ctor_set(v___x_4686_, 1, v___x_4685_);
        v___x_4687_ = leanh::lean_box(0);
        v___x_4688_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4688_, 0, v___x_4686_);
        leanh::lean_ctor_set(v___x_4688_, 1, v___x_4687_);
        return v___x_4688_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(
    mut v_x_4689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_range_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fullRange_x3f_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_x3f_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_x3f_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_x3f_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_x3f_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_message_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTags_x3f_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relatedInformation_x3f_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_4690_ = leanh::lean_ctor_get(v_x_4689_, 0);
    leanh::lean_inc_ref(v_range_4690_);
    v_fullRange_x3f_4691_ = leanh::lean_ctor_get(v_x_4689_, 1);
    leanh::lean_inc(v_fullRange_x3f_4691_);
    v_severity_x3f_4692_ = leanh::lean_ctor_get(v_x_4689_, 2);
    leanh::lean_inc(v_severity_x3f_4692_);
    v_isSilent_x3f_4693_ = leanh::lean_ctor_get(v_x_4689_, 3);
    leanh::lean_inc(v_isSilent_x3f_4693_);
    v_code_x3f_4694_ = leanh::lean_ctor_get(v_x_4689_, 4);
    leanh::lean_inc(v_code_x3f_4694_);
    v_source_x3f_4695_ = leanh::lean_ctor_get(v_x_4689_, 5);
    leanh::lean_inc(v_source_x3f_4695_);
    v_message_4696_ = leanh::lean_ctor_get(v_x_4689_, 6);
    leanh::lean_inc(v_message_4696_);
    v_tags_x3f_4697_ = leanh::lean_ctor_get(v_x_4689_, 7);
    leanh::lean_inc(v_tags_x3f_4697_);
    v_leanTags_x3f_4698_ = leanh::lean_ctor_get(v_x_4689_, 8);
    leanh::lean_inc(v_leanTags_x3f_4698_);
    v_relatedInformation_x3f_4699_ = leanh::lean_ctor_get(v_x_4689_, 9);
    leanh::lean_inc(v_relatedInformation_x3f_4699_);
    v_data_x3f_4700_ = leanh::lean_ctor_get(v_x_4689_, 10);
    leanh::lean_inc(v_data_x3f_4700_);
    leanh::lean_dec_ref(v_x_4689_);
    v___x_4701_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7;
    v___x_4702_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_4690_);
    v___x_4703_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4703_, 0, v___x_4701_);
    leanh::lean_ctor_set(v___x_4703_, 1, v___x_4702_);
    v___x_4704_ = leanh::lean_box(0);
    v___x_4705_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4705_, 0, v___x_4703_);
    leanh::lean_ctor_set(v___x_4705_, 1, v___x_4704_);
    v___x_4706_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8;
    v___x_4707_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(v___x_4706_, v_fullRange_x3f_4691_);
    v___x_4708_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9;
    v___x_4709_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v___x_4708_, v_severity_x3f_4692_);
    leanh::lean_dec(v_severity_x3f_4692_);
    v___x_4710_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10;
    v___x_4711_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(
            v___x_4710_,
            v_isSilent_x3f_4693_,
        );
    leanh::lean_dec(v_isSilent_x3f_4693_);
    v___x_4712_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11;
    v___x_4713_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(v___x_4712_, v_code_x3f_4694_);
    v___x_4714_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12;
    v___x_4715_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(v___x_4714_, v_source_x3f_4695_);
    v___x_4716_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
    v___x_4717_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4717_, 0, v_message_4696_);
    v___x_4718_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4718_, 0, v___x_4716_);
    leanh::lean_ctor_set(v___x_4718_, 1, v___x_4717_);
    v___x_4719_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4719_, 0, v___x_4718_);
    leanh::lean_ctor_set(v___x_4719_, 1, v___x_4704_);
    v___x_4720_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13;
    v___x_4721_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(v___x_4720_, v_tags_x3f_4697_);
    v___x_4722_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14;
    v___x_4723_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(v___x_4722_, v_leanTags_x3f_4698_);
    v___x_4724_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15;
    v___x_4725_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(v___x_4724_, v_relatedInformation_x3f_4699_);
    v___x_4726_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16;
    v___x_4727_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v___x_4726_, v_data_x3f_4700_);
    leanh::lean_dec(v_data_x3f_4700_);
    v___x_4728_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4728_, 0, v___x_4727_);
    leanh::lean_ctor_set(v___x_4728_, 1, v___x_4704_);
    v___x_4729_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4729_, 0, v___x_4725_);
    leanh::lean_ctor_set(v___x_4729_, 1, v___x_4728_);
    v___x_4730_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4730_, 0, v___x_4723_);
    leanh::lean_ctor_set(v___x_4730_, 1, v___x_4729_);
    v___x_4731_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4731_, 0, v___x_4721_);
    leanh::lean_ctor_set(v___x_4731_, 1, v___x_4730_);
    v___x_4732_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4732_, 0, v___x_4719_);
    leanh::lean_ctor_set(v___x_4732_, 1, v___x_4731_);
    v___x_4733_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4733_, 0, v___x_4715_);
    leanh::lean_ctor_set(v___x_4733_, 1, v___x_4732_);
    v___x_4734_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4734_, 0, v___x_4713_);
    leanh::lean_ctor_set(v___x_4734_, 1, v___x_4733_);
    v___x_4735_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4735_, 0, v___x_4711_);
    leanh::lean_ctor_set(v___x_4735_, 1, v___x_4734_);
    v___x_4736_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4736_, 0, v___x_4709_);
    leanh::lean_ctor_set(v___x_4736_, 1, v___x_4735_);
    v___x_4737_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4737_, 0, v___x_4707_);
    leanh::lean_ctor_set(v___x_4737_, 1, v___x_4736_);
    v___x_4738_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4738_, 0, v___x_4705_);
    leanh::lean_ctor_set(v___x_4738_, 1, v___x_4737_);
    v___x_4739_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2;
    v___x_4740_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_4738_, v___x_4739_);
    v___x_4741_ = l_Lean_Json_mkObj(v___x_4740_);
    leanh::lean_dec(v___x_4740_);
    return v___x_4741_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(
    mut v_sz_4742_: usize,
    mut v_i_4743_: usize,
    mut v_bs_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4745_: u8 = 0;
    let mut v_v_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: usize = 0;
    let mut v___x_4751_: usize = 0;
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4745_ = lean_usize_dec_lt(v_i_4743_, v_sz_4742_);
                if v___x_4745_ == 0 {
                    return v_bs_4744_;
                } else {
                    v_v_4746_ = lean_array_uget(v_bs_4744_, v_i_4743_);
                    v___x_4747_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_4754_: *mut leanh::LeanObject,
    mut v_i_4755_: *mut leanh::LeanObject,
    mut v_bs_4756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4757_: usize = 0;
    let mut v_i_boxed_4758_: usize = 0;
    let mut v_res_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4757_ = leanh::lean_unbox_usize(v_sz_4754_);
    leanh::lean_dec(v_sz_4754_);
    v_i_boxed_4758_ = leanh::lean_unbox_usize(v_i_4755_);
    leanh::lean_dec(v_i_4755_);
    v_res_4759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_boxed_4757_, v_i_boxed_4758_, v_bs_4756_);
    return v_res_4759_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(
    mut v_a_4760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4761_: usize = 0;
    let mut v___x_4762_: usize = 0;
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4761_ = lean_array_size(v_a_4760_);
    v___x_4762_ = 0usize;
    v___x_4763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_4761_, v___x_4762_, v_a_4760_);
    v___x_4764_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4764_, 0, v___x_4763_);
    return v___x_4764_;
}
pub unsafe fn l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(
    mut v_x_4769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_uri_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isIncremental_x3f_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diagnostics_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_uri_4770_ = leanh::lean_ctor_get(v_x_4769_, 0);
    leanh::lean_inc_ref(v_uri_4770_);
    v_version_x3f_4771_ = leanh::lean_ctor_get(v_x_4769_, 1);
    leanh::lean_inc(v_version_x3f_4771_);
    v_isIncremental_x3f_4772_ = leanh::lean_ctor_get(v_x_4769_, 2);
    leanh::lean_inc(v_isIncremental_x3f_4772_);
    v_diagnostics_4773_ = leanh::lean_ctor_get(v_x_4769_, 3);
    leanh::lean_inc_ref(v_diagnostics_4773_);
    leanh::lean_dec_ref(v_x_4769_);
    v___x_4774_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0;
    v___x_4775_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4775_, 0, v_uri_4770_);
    v___x_4776_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4776_, 0, v___x_4774_);
    leanh::lean_ctor_set(v___x_4776_, 1, v___x_4775_);
    v___x_4777_ = leanh::lean_box(0);
    v___x_4778_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4778_, 0, v___x_4776_);
    leanh::lean_ctor_set(v___x_4778_, 1, v___x_4777_);
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
    leanh::lean_dec(v_isIncremental_x3f_4772_);
    v___x_4783_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3;
    v___x_4784_ =
        l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(
            v_diagnostics_4773_,
        );
    v___x_4785_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4785_, 0, v___x_4783_);
    leanh::lean_ctor_set(v___x_4785_, 1, v___x_4784_);
    v___x_4786_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4786_, 0, v___x_4785_);
    leanh::lean_ctor_set(v___x_4786_, 1, v___x_4777_);
    v___x_4787_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4787_, 0, v___x_4786_);
    leanh::lean_ctor_set(v___x_4787_, 1, v___x_4777_);
    v___x_4788_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4788_, 0, v___x_4782_);
    leanh::lean_ctor_set(v___x_4788_, 1, v___x_4787_);
    v___x_4789_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4789_, 0, v___x_4780_);
    leanh::lean_ctor_set(v___x_4789_, 1, v___x_4788_);
    v___x_4790_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4790_, 0, v___x_4778_);
    leanh::lean_ctor_set(v___x_4790_, 1, v___x_4789_);
    v___x_4791_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2;
    v___x_4792_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_4790_, v___x_4791_);
    v___x_4793_ = l_Lean_Json_mkObj(v___x_4792_);
    leanh::lean_dec(v___x_4792_);
    return v___x_4793_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(
    mut v_x_4798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4804_: u8 = 0;
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut v_a_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4812_: u8 = 0;
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4798_) == 0 {
                    v___x_4799_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0;
                    return v___x_4799_;
                } else {
                    v___x_4800_ = l_Lean_Json_getBool_x3f(v_x_4798_);
                    if leanh::lean_obj_tag(v___x_4800_) == 0 {
                        v_a_4801_ = leanh::lean_ctor_get(v___x_4800_, 0);
                        v_isSharedCheck_4808_ =
                            (!leanh::lean_is_exclusive(v___x_4800_)) as u8;
                        if v_isSharedCheck_4808_ == 0 {
                            v___x_4803_ = v___x_4800_;
                            v_isShared_4804_ = v_isSharedCheck_4808_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4801_);
                            leanh::lean_dec(v___x_4800_);
                            v___x_4803_ = leanh::lean_box(0);
                            v_isShared_4804_ = v_isSharedCheck_4808_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4809_ = leanh::lean_ctor_get(v___x_4800_, 0);
                        v_isSharedCheck_4817_ =
                            (!leanh::lean_is_exclusive(v___x_4800_)) as u8;
                        if v_isSharedCheck_4817_ == 0 {
                            v___x_4811_ = v___x_4800_;
                            v_isShared_4812_ = v_isSharedCheck_4817_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4809_);
                            leanh::lean_dec(v___x_4800_);
                            v___x_4811_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
                    v___x_4806_ = v_reuseFailAlloc_4807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4806_;
            }
            3 => {
                v___x_4813_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4813_, 0, v_a_4809_);
                if v_isShared_4812_ == 0 {
                    leanh::lean_ctor_set(v___x_4811_, 0, v___x_4813_);
                    v___x_4815_ = v___x_4811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
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
    mut v_x_4818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4819_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v_x_4818_);
    leanh::lean_dec(v_x_4818_);
    return v_res_4819_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(
    mut v_j_4820_: *mut leanh::LeanObject,
    mut v_k_4821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4822_ = l_Lean_Json_getObjValD(v_j_4820_, v_k_4821_);
    v___x_4823_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v___x_4822_);
    leanh::lean_dec(v___x_4822_);
    return v___x_4823_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(
    mut v_j_4824_: *mut leanh::LeanObject,
    mut v_k_4825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4826_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_j_4824_, v_k_4825_);
    leanh::lean_dec_ref(v_k_4825_);
    return v_res_4826_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(
    mut v_x_4829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4835_: u8 = 0;
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut v_a_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4843_: u8 = 0;
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4829_) == 0 {
                    v___x_4830_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0;
                    return v___x_4830_;
                } else {
                    v___x_4831_ = l_Lean_Json_getInt_x3f(v_x_4829_);
                    if leanh::lean_obj_tag(v___x_4831_) == 0 {
                        v_a_4832_ = leanh::lean_ctor_get(v___x_4831_, 0);
                        v_isSharedCheck_4839_ =
                            (!leanh::lean_is_exclusive(v___x_4831_)) as u8;
                        if v_isSharedCheck_4839_ == 0 {
                            v___x_4834_ = v___x_4831_;
                            v_isShared_4835_ = v_isSharedCheck_4839_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4832_);
                            leanh::lean_dec(v___x_4831_);
                            v___x_4834_ = leanh::lean_box(0);
                            v_isShared_4835_ = v_isSharedCheck_4839_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4840_ = leanh::lean_ctor_get(v___x_4831_, 0);
                        v_isSharedCheck_4848_ =
                            (!leanh::lean_is_exclusive(v___x_4831_)) as u8;
                        if v_isSharedCheck_4848_ == 0 {
                            v___x_4842_ = v___x_4831_;
                            v_isShared_4843_ = v_isSharedCheck_4848_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4840_);
                            leanh::lean_dec(v___x_4831_);
                            v___x_4842_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4838_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
                    v___x_4837_ = v_reuseFailAlloc_4838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4837_;
            }
            3 => {
                v___x_4844_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4844_, 0, v_a_4840_);
                if v_isShared_4843_ == 0 {
                    leanh::lean_ctor_set(v___x_4842_, 0, v___x_4844_);
                    v___x_4846_ = v___x_4842_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4847_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4844_);
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
    mut v_j_4849_: *mut leanh::LeanObject,
    mut v_k_4850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4851_ = l_Lean_Json_getObjValD(v_j_4849_, v_k_4850_);
    v___x_4852_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(v___x_4851_);
    return v___x_4852_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(
    mut v_j_4853_: *mut leanh::LeanObject,
    mut v_k_4854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4855_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_j_4853_, v_k_4854_);
    leanh::lean_dec_ref(v_k_4854_);
    return v_res_4855_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(
    mut v_x_4858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4858_) == 0 {
        let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4859_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0;
        return v___x_4859_;
    } else {
        let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4860_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4860_, 0, v_x_4858_);
        v___x_4861_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4861_, 0, v___x_4860_);
        return v___x_4861_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(
    mut v_j_4862_: *mut leanh::LeanObject,
    mut v_k_4863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4864_ = l_Lean_Json_getObjValD(v_j_4862_, v_k_4863_);
    v___x_4865_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(v___x_4864_);
    return v___x_4865_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14___boxed(
    mut v_j_4866_: *mut leanh::LeanObject,
    mut v_k_4867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4868_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_j_4866_, v_k_4867_);
    leanh::lean_dec_ref(v_k_4867_);
    return v_res_4868_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(
    mut v_sz_4871_: usize,
    mut v_i_4872_: usize,
    mut v_bs_4873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u8 = 0;
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: u8 = 0;
    let mut v___x_4885_: usize = 0;
    let mut v___x_4886_: usize = 0;
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: u8 = 0;
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: u8 = 0;
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4876_ = lean_usize_dec_lt(v_i_4872_, v_sz_4871_);
                if v___x_4876_ == 0 {
                    v___x_4877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4877_, 0, v_bs_4873_);
                    return v___x_4877_;
                } else {
                    v_v_4878_ = lean_array_uget_borrowed(v_bs_4873_, v_i_4872_);
                    leanh::lean_inc(v_v_4878_);
                    v___x_4879_ = l_Lean_Json_getNat_x3f(v_v_4878_);
                    if leanh::lean_obj_tag(v___x_4879_) == 1 {
                        v_a_4880_ = leanh::lean_ctor_get(v___x_4879_, 0);
                        leanh::lean_inc(v_a_4880_);
                        leanh::lean_dec_ref_known(v___x_4879_, 1);
                        v___x_4881_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4882_ = lean_array_uset(v_bs_4873_, v_i_4872_, v___x_4881_);
                        v___x_4890_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4891_ = lean_nat_dec_eq(v_a_4880_, v___x_4890_);
                        if v___x_4891_ == 0 {
                            v___x_4892_ = leanh::lean_unsigned_to_nat(2);
                            v___x_4893_ = lean_nat_dec_eq(v_a_4880_, v___x_4892_);
                            leanh::lean_dec(v_a_4880_);
                            if v___x_4893_ == 0 {
                                leanh::lean_dec_ref(v_bs_x27_4882_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4894_ = 1;
                                v_a_4884_ = v___x_4894_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4880_);
                            v___x_4895_ = 0;
                            v_a_4884_ = v___x_4895_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_4879_);
                        leanh::lean_dec_ref(v_bs_4873_);
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
                v___x_4887_ = leanh::lean_box((v_a_4884_) as usize);
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
    mut v_sz_4896_: *mut leanh::LeanObject,
    mut v_i_4897_: *mut leanh::LeanObject,
    mut v_bs_4898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4899_: usize = 0;
    let mut v_i_boxed_4900_: usize = 0;
    let mut v_res_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4899_ = leanh::lean_unbox_usize(v_sz_4896_);
    leanh::lean_dec(v_sz_4896_);
    v_i_boxed_4900_ = leanh::lean_unbox_usize(v_i_4897_);
    leanh::lean_dec(v_i_4897_);
    v_res_4901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_boxed_4899_, v_i_boxed_4900_, v_bs_4898_);
    return v_res_4901_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(
    mut v_x_4903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4903_) == 4 {
        let mut v_elems_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4905_: usize = 0;
        let mut v___x_4906_: usize = 0;
        let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_4904_ = leanh::lean_ctor_get(v_x_4903_, 0);
        leanh::lean_inc_ref(v_elems_4904_);
        leanh::lean_dec_ref_known(v_x_4903_, 1);
        v_sz_4905_ = lean_array_size(v_elems_4904_);
        v___x_4906_ = 0usize;
        v___x_4907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_4905_, v___x_4906_, v_elems_4904_);
        return v___x_4907_;
    } else {
        let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4908_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0;
        v___x_4909_ = leanh::lean_unsigned_to_nat(80);
        v___x_4910_ = l_Lean_Json_pretty(v_x_4903_, v___x_4909_);
        v___x_4911_ = lean_string_append(v___x_4908_, v___x_4910_);
        leanh::lean_dec_ref(v___x_4910_);
        v___x_4912_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
        v___x_4913_ = lean_string_append(v___x_4911_, v___x_4912_);
        v___x_4914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4914_, 0, v___x_4913_);
        return v___x_4914_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(
    mut v_x_4917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4923_: u8 = 0;
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4927_: u8 = 0;
    let mut v_a_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4931_: u8 = 0;
    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4917_) == 0 {
                    v___x_4918_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0;
                    return v___x_4918_;
                } else {
                    v___x_4919_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(v_x_4917_);
                    if leanh::lean_obj_tag(v___x_4919_) == 0 {
                        v_a_4920_ = leanh::lean_ctor_get(v___x_4919_, 0);
                        v_isSharedCheck_4927_ =
                            (!leanh::lean_is_exclusive(v___x_4919_)) as u8;
                        if v_isSharedCheck_4927_ == 0 {
                            v___x_4922_ = v___x_4919_;
                            v_isShared_4923_ = v_isSharedCheck_4927_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4920_);
                            leanh::lean_dec(v___x_4919_);
                            v___x_4922_ = leanh::lean_box(0);
                            v_isShared_4923_ = v_isSharedCheck_4927_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4928_ = leanh::lean_ctor_get(v___x_4919_, 0);
                        v_isSharedCheck_4936_ =
                            (!leanh::lean_is_exclusive(v___x_4919_)) as u8;
                        if v_isSharedCheck_4936_ == 0 {
                            v___x_4930_ = v___x_4919_;
                            v_isShared_4931_ = v_isSharedCheck_4936_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4928_);
                            leanh::lean_dec(v___x_4919_);
                            v___x_4930_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4926_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
                    v___x_4925_ = v_reuseFailAlloc_4926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4925_;
            }
            3 => {
                v___x_4932_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4932_, 0, v_a_4928_);
                if v_isShared_4931_ == 0 {
                    leanh::lean_ctor_set(v___x_4930_, 0, v___x_4932_);
                    v___x_4934_ = v___x_4930_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4935_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
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
    mut v_j_4937_: *mut leanh::LeanObject,
    mut v_k_4938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4939_ = l_Lean_Json_getObjValD(v_j_4937_, v_k_4938_);
    v___x_4940_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(v___x_4939_);
    return v___x_4940_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12___boxed(
    mut v_j_4941_: *mut leanh::LeanObject,
    mut v_k_4942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4943_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_j_4941_, v_k_4942_);
    leanh::lean_dec_ref(v_k_4942_);
    return v_res_4943_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(
    mut v_x_4946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: u8 = 0;
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4946_) == 0 {
                    v___x_4960_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0;
                    return v___x_4960_;
                } else {
                    match leanh::lean_obj_tag(v_x_4946_) {
                        2 => {
                            v_n_4961_ = leanh::lean_ctor_get(v_x_4946_, 0);
                            v_mantissa_4962_ = leanh::lean_ctor_get(v_n_4961_, 0);
                            v_exponent_4963_ = leanh::lean_ctor_get(v_n_4961_, 1);
                            v___x_4964_ = leanh::lean_unsigned_to_nat(0);
                            v___x_4965_ = lean_nat_dec_eq(v_exponent_4963_, v___x_4964_);
                            if v___x_4965_ == 0 {
                                v_j_4952_ = v_x_4946_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_mantissa_4962_);
                                leanh::lean_dec_ref_known(v_x_4946_, 1);
                                v___x_4966_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4966_, 0, v_mantissa_4962_);
                                v_a_4948_ = v___x_4966_;
                                state = 1;
                                continue;
                            }
                        }
                        3 => {
                            v_s_4967_ = leanh::lean_ctor_get(v_x_4946_, 0);
                            leanh::lean_inc_ref(v_s_4967_);
                            leanh::lean_dec_ref_known(v_x_4946_, 1);
                            v___x_4968_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4968_, 0, v_s_4967_);
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
                v___x_4949_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4949_, 0, v_a_4948_);
                v___x_4950_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4950_, 0, v___x_4949_);
                return v___x_4950_;
            }
            2 => {
                v___x_4953_ = l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0;
                v___x_4954_ = leanh::lean_unsigned_to_nat(80);
                v___x_4955_ = l_Lean_Json_pretty(v_j_4952_, v___x_4954_);
                v___x_4956_ = lean_string_append(v___x_4953_, v___x_4955_);
                leanh::lean_dec_ref(v___x_4955_);
                v___x_4957_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
                v___x_4958_ = lean_string_append(v___x_4956_, v___x_4957_);
                v___x_4959_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4959_, 0, v___x_4958_);
                return v___x_4959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(
    mut v_j_4969_: *mut leanh::LeanObject,
    mut v_k_4970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4971_ = l_Lean_Json_getObjValD(v_j_4969_, v_k_4970_);
    v___x_4972_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(v___x_4971_);
    return v___x_4972_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9___boxed(
    mut v_j_4973_: *mut leanh::LeanObject,
    mut v_k_4974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4975_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_j_4973_, v_k_4974_);
    leanh::lean_dec_ref(v_k_4974_);
    return v_res_4975_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(
    mut v_j_4976_: *mut leanh::LeanObject,
    mut v_k_4977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4978_ = l_Lean_Json_getObjValD(v_j_4976_, v_k_4977_);
    v___x_4979_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4978_);
    return v___x_4979_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6___boxed(
    mut v_j_4980_: *mut leanh::LeanObject,
    mut v_k_4981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4982_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_j_4980_, v_k_4981_);
    leanh::lean_dec_ref(v_k_4981_);
    return v_res_4982_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(
    mut v_sz_4985_: usize,
    mut v_i_4986_: usize,
    mut v_bs_4987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u8 = 0;
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4998_: u8 = 0;
    let mut v___x_4999_: usize = 0;
    let mut v___x_5000_: usize = 0;
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: u8 = 0;
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: u8 = 0;
    let mut v___x_5008_: u8 = 0;
    let mut v___x_5009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4990_ = lean_usize_dec_lt(v_i_4986_, v_sz_4985_);
                if v___x_4990_ == 0 {
                    v___x_4991_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4991_, 0, v_bs_4987_);
                    return v___x_4991_;
                } else {
                    v_v_4992_ = lean_array_uget_borrowed(v_bs_4987_, v_i_4986_);
                    leanh::lean_inc(v_v_4992_);
                    v___x_4993_ = l_Lean_Json_getNat_x3f(v_v_4992_);
                    if leanh::lean_obj_tag(v___x_4993_) == 1 {
                        v_a_4994_ = leanh::lean_ctor_get(v___x_4993_, 0);
                        leanh::lean_inc(v_a_4994_);
                        leanh::lean_dec_ref_known(v___x_4993_, 1);
                        v___x_4995_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4996_ = lean_array_uset(v_bs_4987_, v_i_4986_, v___x_4995_);
                        v___x_5004_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5005_ = lean_nat_dec_eq(v_a_4994_, v___x_5004_);
                        if v___x_5005_ == 0 {
                            v___x_5006_ = leanh::lean_unsigned_to_nat(2);
                            v___x_5007_ = lean_nat_dec_eq(v_a_4994_, v___x_5006_);
                            leanh::lean_dec(v_a_4994_);
                            if v___x_5007_ == 0 {
                                leanh::lean_dec_ref(v_bs_x27_4996_);
                                state = 1;
                                continue;
                            } else {
                                v___x_5008_ = 1;
                                v_a_4998_ = v___x_5008_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4994_);
                            v___x_5009_ = 0;
                            v_a_4998_ = v___x_5009_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_4993_);
                        leanh::lean_dec_ref(v_bs_4987_);
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
                v___x_5001_ = leanh::lean_box((v_a_4998_) as usize);
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
    mut v_sz_5010_: *mut leanh::LeanObject,
    mut v_i_5011_: *mut leanh::LeanObject,
    mut v_bs_5012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5013_: usize = 0;
    let mut v_i_boxed_5014_: usize = 0;
    let mut v_res_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5013_ = leanh::lean_unbox_usize(v_sz_5010_);
    leanh::lean_dec(v_sz_5010_);
    v_i_boxed_5014_ = leanh::lean_unbox_usize(v_i_5011_);
    leanh::lean_dec(v_i_5011_);
    v_res_5015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_boxed_5013_, v_i_boxed_5014_, v_bs_5012_);
    return v_res_5015_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(
    mut v_x_5016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5016_) == 4 {
        let mut v_elems_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5018_: usize = 0;
        let mut v___x_5019_: usize = 0;
        let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_5017_ = leanh::lean_ctor_get(v_x_5016_, 0);
        leanh::lean_inc_ref(v_elems_5017_);
        leanh::lean_dec_ref_known(v_x_5016_, 1);
        v_sz_5018_ = lean_array_size(v_elems_5017_);
        v___x_5019_ = 0usize;
        v___x_5020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_5018_, v___x_5019_, v_elems_5017_);
        return v___x_5020_;
    } else {
        let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5021_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0;
        v___x_5022_ = leanh::lean_unsigned_to_nat(80);
        v___x_5023_ = l_Lean_Json_pretty(v_x_5016_, v___x_5022_);
        v___x_5024_ = lean_string_append(v___x_5021_, v___x_5023_);
        leanh::lean_dec_ref(v___x_5023_);
        v___x_5025_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
        v___x_5026_ = lean_string_append(v___x_5024_, v___x_5025_);
        v___x_5027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5027_, 0, v___x_5026_);
        return v___x_5027_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(
    mut v_x_5030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5036_: u8 = 0;
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5040_: u8 = 0;
    let mut v_a_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5030_) == 0 {
                    v___x_5031_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0;
                    return v___x_5031_;
                } else {
                    v___x_5032_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(v_x_5030_);
                    if leanh::lean_obj_tag(v___x_5032_) == 0 {
                        v_a_5033_ = leanh::lean_ctor_get(v___x_5032_, 0);
                        v_isSharedCheck_5040_ =
                            (!leanh::lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5040_ == 0 {
                            v___x_5035_ = v___x_5032_;
                            v_isShared_5036_ = v_isSharedCheck_5040_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5033_);
                            leanh::lean_dec(v___x_5032_);
                            v___x_5035_ = leanh::lean_box(0);
                            v_isShared_5036_ = v_isSharedCheck_5040_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5041_ = leanh::lean_ctor_get(v___x_5032_, 0);
                        v_isSharedCheck_5049_ =
                            (!leanh::lean_is_exclusive(v___x_5032_)) as u8;
                        if v_isSharedCheck_5049_ == 0 {
                            v___x_5043_ = v___x_5032_;
                            v_isShared_5044_ = v_isSharedCheck_5049_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5041_);
                            leanh::lean_dec(v___x_5032_);
                            v___x_5043_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5039_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
                    v___x_5038_ = v_reuseFailAlloc_5039_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5038_;
            }
            3 => {
                v___x_5045_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5045_, 0, v_a_5041_);
                if v_isShared_5044_ == 0 {
                    leanh::lean_ctor_set(v___x_5043_, 0, v___x_5045_);
                    v___x_5047_ = v___x_5043_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5048_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5045_);
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
    mut v_j_5050_: *mut leanh::LeanObject,
    mut v_k_5051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Lean_Json_getObjValD(v_j_5050_, v_k_5051_);
    v___x_5053_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(v___x_5052_);
    return v___x_5053_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11___boxed(
    mut v_j_5054_: *mut leanh::LeanObject,
    mut v_k_5055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5056_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_j_5054_, v_k_5055_);
    leanh::lean_dec_ref(v_k_5055_);
    return v_res_5056_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(
    mut v_x_5059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5069_: u8 = 0;
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: u8 = 0;
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: u8 = 0;
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: u8 = 0;
    let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: u8 = 0;
    let mut v___x_5084_: u8 = 0;
    let mut v___x_5085_: u8 = 0;
    let mut v___x_5086_: u8 = 0;
    let mut v___x_5087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5059_) == 0 {
                    v___x_5073_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0;
                    return v___x_5073_;
                } else {
                    leanh::lean_inc(v_x_5059_);
                    v___x_5074_ = l_Lean_Json_getNat_x3f(v_x_5059_);
                    if leanh::lean_obj_tag(v___x_5074_) == 1 {
                        v_a_5075_ = leanh::lean_ctor_get(v___x_5074_, 0);
                        leanh::lean_inc(v_a_5075_);
                        leanh::lean_dec_ref_known(v___x_5074_, 1);
                        v___x_5076_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5077_ = lean_nat_dec_eq(v_a_5075_, v___x_5076_);
                        if v___x_5077_ == 0 {
                            v___x_5078_ = leanh::lean_unsigned_to_nat(2);
                            v___x_5079_ = lean_nat_dec_eq(v_a_5075_, v___x_5078_);
                            if v___x_5079_ == 0 {
                                v___x_5080_ = leanh::lean_unsigned_to_nat(3);
                                v___x_5081_ = lean_nat_dec_eq(v_a_5075_, v___x_5080_);
                                if v___x_5081_ == 0 {
                                    v___x_5082_ = leanh::lean_unsigned_to_nat(4);
                                    v___x_5083_ = lean_nat_dec_eq(v_a_5075_, v___x_5082_);
                                    leanh::lean_dec(v_a_5075_);
                                    if v___x_5083_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_x_5059_);
                                        v___x_5084_ = 3;
                                        v_a_5069_ = v___x_5084_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_5075_);
                                    leanh::lean_dec(v_x_5059_);
                                    v___x_5085_ = 2;
                                    v_a_5069_ = v___x_5085_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5075_);
                                leanh::lean_dec(v_x_5059_);
                                v___x_5086_ = 1;
                                v_a_5069_ = v___x_5086_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5075_);
                            leanh::lean_dec(v_x_5059_);
                            v___x_5087_ = 0;
                            v_a_5069_ = v___x_5087_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_5074_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5061_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0;
                v___x_5062_ = leanh::lean_unsigned_to_nat(80);
                v___x_5063_ = l_Lean_Json_pretty(v_x_5059_, v___x_5062_);
                v___x_5064_ = lean_string_append(v___x_5061_, v___x_5063_);
                leanh::lean_dec_ref(v___x_5063_);
                v___x_5065_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
                v___x_5066_ = lean_string_append(v___x_5064_, v___x_5065_);
                v___x_5067_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5067_, 0, v___x_5066_);
                return v___x_5067_;
            }
            2 => {
                v___x_5070_ = leanh::lean_box((v_a_5069_) as usize);
                v___x_5071_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5071_, 0, v___x_5070_);
                v___x_5072_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5072_, 0, v___x_5071_);
                return v___x_5072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(
    mut v_j_5088_: *mut leanh::LeanObject,
    mut v_k_5089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5090_ = l_Lean_Json_getObjValD(v_j_5088_, v_k_5089_);
    v___x_5091_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(v___x_5090_);
    return v___x_5091_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8___boxed(
    mut v_j_5092_: *mut leanh::LeanObject,
    mut v_k_5093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5094_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_j_5092_, v_k_5093_);
    leanh::lean_dec_ref(v_k_5093_);
    return v_res_5094_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(
    mut v_x_5097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v_a_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5111_: u8 = 0;
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5097_) == 0 {
                    v___x_5098_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0;
                    return v___x_5098_;
                } else {
                    v___x_5099_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_5097_);
                    if leanh::lean_obj_tag(v___x_5099_) == 0 {
                        v_a_5100_ = leanh::lean_ctor_get(v___x_5099_, 0);
                        v_isSharedCheck_5107_ =
                            (!leanh::lean_is_exclusive(v___x_5099_)) as u8;
                        if v_isSharedCheck_5107_ == 0 {
                            v___x_5102_ = v___x_5099_;
                            v_isShared_5103_ = v_isSharedCheck_5107_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5100_);
                            leanh::lean_dec(v___x_5099_);
                            v___x_5102_ = leanh::lean_box(0);
                            v_isShared_5103_ = v_isSharedCheck_5107_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5108_ = leanh::lean_ctor_get(v___x_5099_, 0);
                        v_isSharedCheck_5116_ =
                            (!leanh::lean_is_exclusive(v___x_5099_)) as u8;
                        if v_isSharedCheck_5116_ == 0 {
                            v___x_5110_ = v___x_5099_;
                            v_isShared_5111_ = v_isSharedCheck_5116_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5108_);
                            leanh::lean_dec(v___x_5099_);
                            v___x_5110_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
                    v___x_5105_ = v_reuseFailAlloc_5106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5105_;
            }
            3 => {
                v___x_5112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5112_, 0, v_a_5108_);
                if v_isShared_5111_ == 0 {
                    leanh::lean_ctor_set(v___x_5110_, 0, v___x_5112_);
                    v___x_5114_ = v___x_5110_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5115_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5115_, 0, v___x_5112_);
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
    mut v_j_5117_: *mut leanh::LeanObject,
    mut v_k_5118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5119_ = l_Lean_Json_getObjValD(v_j_5117_, v_k_5118_);
    v___x_5120_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(v___x_5119_);
    return v___x_5120_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7___boxed(
    mut v_j_5121_: *mut leanh::LeanObject,
    mut v_k_5122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5123_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_j_5121_, v_k_5122_);
    leanh::lean_dec_ref(v_k_5122_);
    return v_res_5123_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(
    mut v_sz_5124_: usize,
    mut v_i_5125_: usize,
    mut v_bs_5126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5134_: u8 = 0;
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5138_: u8 = 0;
    let mut v_a_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: usize = 0;
    let mut v___x_5143_: usize = 0;
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5127_ = lean_usize_dec_lt(v_i_5125_, v_sz_5124_);
                if v___x_5127_ == 0 {
                    v___x_5128_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5128_, 0, v_bs_5126_);
                    return v___x_5128_;
                } else {
                    v_v_5129_ = lean_array_uget_borrowed(v_bs_5126_, v_i_5125_);
                    leanh::lean_inc(v_v_5129_);
                    v___x_5130_ =
                        l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_v_5129_);
                    if leanh::lean_obj_tag(v___x_5130_) == 0 {
                        leanh::lean_dec_ref(v_bs_5126_);
                        v_a_5131_ = leanh::lean_ctor_get(v___x_5130_, 0);
                        v_isSharedCheck_5138_ =
                            (!leanh::lean_is_exclusive(v___x_5130_)) as u8;
                        if v_isSharedCheck_5138_ == 0 {
                            v___x_5133_ = v___x_5130_;
                            v_isShared_5134_ = v_isSharedCheck_5138_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5131_);
                            leanh::lean_dec(v___x_5130_);
                            v___x_5133_ = leanh::lean_box(0);
                            v_isShared_5134_ = v_isSharedCheck_5138_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5139_ = leanh::lean_ctor_get(v___x_5130_, 0);
                        leanh::lean_inc(v_a_5139_);
                        leanh::lean_dec_ref_known(v___x_5130_, 1);
                        v___x_5140_ = leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_5137_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_a_5131_);
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
    mut v_sz_5146_: *mut leanh::LeanObject,
    mut v_i_5147_: *mut leanh::LeanObject,
    mut v_bs_5148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5149_: usize = 0;
    let mut v_i_boxed_5150_: usize = 0;
    let mut v_res_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5149_ = leanh::lean_unbox_usize(v_sz_5146_);
    leanh::lean_dec(v_sz_5146_);
    v_i_boxed_5150_ = leanh::lean_unbox_usize(v_i_5147_);
    leanh::lean_dec(v_i_5147_);
    v_res_5151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_boxed_5149_, v_i_boxed_5150_, v_bs_5148_);
    return v_res_5151_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(
    mut v_x_5152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5152_) == 4 {
        let mut v_elems_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5154_: usize = 0;
        let mut v___x_5155_: usize = 0;
        let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_5153_ = leanh::lean_ctor_get(v_x_5152_, 0);
        leanh::lean_inc_ref(v_elems_5153_);
        leanh::lean_dec_ref_known(v_x_5152_, 1);
        v_sz_5154_ = lean_array_size(v_elems_5153_);
        v___x_5155_ = 0usize;
        v___x_5156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_5154_, v___x_5155_, v_elems_5153_);
        return v___x_5156_;
    } else {
        let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5157_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0;
        v___x_5158_ = leanh::lean_unsigned_to_nat(80);
        v___x_5159_ = l_Lean_Json_pretty(v_x_5152_, v___x_5158_);
        v___x_5160_ = lean_string_append(v___x_5157_, v___x_5159_);
        leanh::lean_dec_ref(v___x_5159_);
        v___x_5161_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
        v___x_5162_ = lean_string_append(v___x_5160_, v___x_5161_);
        v___x_5163_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5163_, 0, v___x_5162_);
        return v___x_5163_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(
    mut v_x_5166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5172_: u8 = 0;
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut v_a_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5166_) == 0 {
                    v___x_5167_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0;
                    return v___x_5167_;
                } else {
                    v___x_5168_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(v_x_5166_);
                    if leanh::lean_obj_tag(v___x_5168_) == 0 {
                        v_a_5169_ = leanh::lean_ctor_get(v___x_5168_, 0);
                        v_isSharedCheck_5176_ =
                            (!leanh::lean_is_exclusive(v___x_5168_)) as u8;
                        if v_isSharedCheck_5176_ == 0 {
                            v___x_5171_ = v___x_5168_;
                            v_isShared_5172_ = v_isSharedCheck_5176_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5169_);
                            leanh::lean_dec(v___x_5168_);
                            v___x_5171_ = leanh::lean_box(0);
                            v_isShared_5172_ = v_isSharedCheck_5176_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5177_ = leanh::lean_ctor_get(v___x_5168_, 0);
                        v_isSharedCheck_5185_ =
                            (!leanh::lean_is_exclusive(v___x_5168_)) as u8;
                        if v_isSharedCheck_5185_ == 0 {
                            v___x_5179_ = v___x_5168_;
                            v_isShared_5180_ = v_isSharedCheck_5185_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5177_);
                            leanh::lean_dec(v___x_5168_);
                            v___x_5179_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5175_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
                    v___x_5174_ = v_reuseFailAlloc_5175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5174_;
            }
            3 => {
                v___x_5181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5181_, 0, v_a_5177_);
                if v_isShared_5180_ == 0 {
                    leanh::lean_ctor_set(v___x_5179_, 0, v___x_5181_);
                    v___x_5183_ = v___x_5179_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5184_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
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
    mut v_j_5186_: *mut leanh::LeanObject,
    mut v_k_5187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5188_ = l_Lean_Json_getObjValD(v_j_5186_, v_k_5187_);
    v___x_5189_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(v___x_5188_);
    return v___x_5189_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13___boxed(
    mut v_j_5190_: *mut leanh::LeanObject,
    mut v_k_5191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5192_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_j_5190_, v_k_5191_);
    leanh::lean_dec_ref(v_k_5191_);
    return v_res_5192_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(
    mut v_x_5195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut v_a_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5209_: u8 = 0;
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5195_) == 0 {
                    v___x_5196_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0;
                    return v___x_5196_;
                } else {
                    v___x_5197_ = l_Lean_Json_getStr_x3f(v_x_5195_);
                    if leanh::lean_obj_tag(v___x_5197_) == 0 {
                        v_a_5198_ = leanh::lean_ctor_get(v___x_5197_, 0);
                        v_isSharedCheck_5205_ =
                            (!leanh::lean_is_exclusive(v___x_5197_)) as u8;
                        if v_isSharedCheck_5205_ == 0 {
                            v___x_5200_ = v___x_5197_;
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5198_);
                            leanh::lean_dec(v___x_5197_);
                            v___x_5200_ = leanh::lean_box(0);
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5206_ = leanh::lean_ctor_get(v___x_5197_, 0);
                        v_isSharedCheck_5214_ =
                            (!leanh::lean_is_exclusive(v___x_5197_)) as u8;
                        if v_isSharedCheck_5214_ == 0 {
                            v___x_5208_ = v___x_5197_;
                            v_isShared_5209_ = v_isSharedCheck_5214_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5206_);
                            leanh::lean_dec(v___x_5197_);
                            v___x_5208_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5204_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
                    v___x_5203_ = v_reuseFailAlloc_5204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5203_;
            }
            3 => {
                v___x_5210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5210_, 0, v_a_5206_);
                if v_isShared_5209_ == 0 {
                    leanh::lean_ctor_set(v___x_5208_, 0, v___x_5210_);
                    v___x_5212_ = v___x_5208_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5213_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5210_);
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
    mut v_j_5215_: *mut leanh::LeanObject,
    mut v_k_5216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5217_ = l_Lean_Json_getObjValD(v_j_5215_, v_k_5216_);
    v___x_5218_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(v___x_5217_);
    return v___x_5218_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10___boxed(
    mut v_j_5219_: *mut leanh::LeanObject,
    mut v_k_5220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5221_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_j_5219_, v_k_5220_);
    leanh::lean_dec_ref(v_k_5220_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(
    mut v_json_5222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5228_: u8 = 0;
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5234_: u8 = 0;
    let mut v_a_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5242_: u8 = 0;
    let mut v_a_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v_a_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5259_: u8 = 0;
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5263_: u8 = 0;
    let mut v_a_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5270_: u8 = 0;
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5276_: u8 = 0;
    let mut v_a_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5280_: u8 = 0;
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut v_a_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5291_: u8 = 0;
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5297_: u8 = 0;
    let mut v_a_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut v_a_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5318_: u8 = 0;
    let mut v_a_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5326_: u8 = 0;
    let mut v_a_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5339_: u8 = 0;
    let mut v_a_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5343_: u8 = 0;
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v_a_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut v_a_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5368_: u8 = 0;
    let mut v_a_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5375_: u8 = 0;
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5381_: u8 = 0;
    let mut v_a_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5385_: u8 = 0;
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5389_: u8 = 0;
    let mut v_a_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5402_: u8 = 0;
    let mut v_a_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5406_: u8 = 0;
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5410_: u8 = 0;
    let mut v_a_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5417_: u8 = 0;
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5423_: u8 = 0;
    let mut v_a_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5427_: u8 = 0;
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5431_: u8 = 0;
    let mut v_a_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5438_: u8 = 0;
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5223_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7;
                leanh::lean_inc(v_json_5222_);
                v___x_5224_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_json_5222_, v___x_5223_);
                if leanh::lean_obj_tag(v___x_5224_) == 0 {
                    leanh::lean_dec(v_json_5222_);
                    v_a_5225_ = leanh::lean_ctor_get(v___x_5224_, 0);
                    v_isSharedCheck_5234_ = (!leanh::lean_is_exclusive(v___x_5224_)) as u8;
                    if v_isSharedCheck_5234_ == 0 {
                        v___x_5227_ = v___x_5224_;
                        v_isShared_5228_ = v_isSharedCheck_5234_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5225_);
                        leanh::lean_dec(v___x_5224_);
                        v___x_5227_ = leanh::lean_box(0);
                        v_isShared_5228_ = v_isSharedCheck_5234_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_5224_) == 0 {
                        leanh::lean_dec(v_json_5222_);
                        v_a_5235_ = leanh::lean_ctor_get(v___x_5224_, 0);
                        v_isSharedCheck_5242_ =
                            (!leanh::lean_is_exclusive(v___x_5224_)) as u8;
                        if v_isSharedCheck_5242_ == 0 {
                            v___x_5237_ = v___x_5224_;
                            v_isShared_5238_ = v_isSharedCheck_5242_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5235_);
                            leanh::lean_dec(v___x_5224_);
                            v___x_5237_ = leanh::lean_box(0);
                            v_isShared_5238_ = v_isSharedCheck_5242_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5243_ = leanh::lean_ctor_get(v___x_5224_, 0);
                        leanh::lean_inc(v_a_5243_);
                        leanh::lean_dec_ref_known(v___x_5224_, 1);
                        v___x_5244_ =
                            l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8;
                        leanh::lean_inc(v_json_5222_);
                        v___x_5245_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_json_5222_, v___x_5244_);
                        if leanh::lean_obj_tag(v___x_5245_) == 0 {
                            leanh::lean_dec(v_a_5243_);
                            leanh::lean_dec(v_json_5222_);
                            v_a_5246_ = leanh::lean_ctor_get(v___x_5245_, 0);
                            v_isSharedCheck_5255_ =
                                (!leanh::lean_is_exclusive(v___x_5245_)) as u8;
                            if v_isSharedCheck_5255_ == 0 {
                                v___x_5248_ = v___x_5245_;
                                v_isShared_5249_ = v_isSharedCheck_5255_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5246_);
                                leanh::lean_dec(v___x_5245_);
                                v___x_5248_ = leanh::lean_box(0);
                                v_isShared_5249_ = v_isSharedCheck_5255_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_5245_) == 0 {
                                leanh::lean_dec(v_a_5243_);
                                leanh::lean_dec(v_json_5222_);
                                v_a_5256_ = leanh::lean_ctor_get(v___x_5245_, 0);
                                v_isSharedCheck_5263_ =
                                    (!leanh::lean_is_exclusive(v___x_5245_)) as u8;
                                if v_isSharedCheck_5263_ == 0 {
                                    v___x_5258_ = v___x_5245_;
                                    v_isShared_5259_ = v_isSharedCheck_5263_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5256_);
                                    leanh::lean_dec(v___x_5245_);
                                    v___x_5258_ = leanh::lean_box(0);
                                    v_isShared_5259_ = v_isSharedCheck_5263_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5264_ = leanh::lean_ctor_get(v___x_5245_, 0);
                                leanh::lean_inc(v_a_5264_);
                                leanh::lean_dec_ref_known(v___x_5245_, 1);
                                v___x_5265_ =
                                    l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9;
                                leanh::lean_inc(v_json_5222_);
                                v___x_5266_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_json_5222_, v___x_5265_);
                                if leanh::lean_obj_tag(v___x_5266_) == 0 {
                                    leanh::lean_dec(v_a_5264_);
                                    leanh::lean_dec(v_a_5243_);
                                    leanh::lean_dec(v_json_5222_);
                                    v_a_5267_ = leanh::lean_ctor_get(v___x_5266_, 0);
                                    v_isSharedCheck_5276_ =
                                        (!leanh::lean_is_exclusive(v___x_5266_)) as u8;
                                    if v_isSharedCheck_5276_ == 0 {
                                        v___x_5269_ = v___x_5266_;
                                        v_isShared_5270_ = v_isSharedCheck_5276_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5267_);
                                        leanh::lean_dec(v___x_5266_);
                                        v___x_5269_ = leanh::lean_box(0);
                                        v_isShared_5270_ = v_isSharedCheck_5276_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_5266_) == 0 {
                                        leanh::lean_dec(v_a_5264_);
                                        leanh::lean_dec(v_a_5243_);
                                        leanh::lean_dec(v_json_5222_);
                                        v_a_5277_ = leanh::lean_ctor_get(v___x_5266_, 0);
                                        v_isSharedCheck_5284_ =
                                            (!leanh::lean_is_exclusive(v___x_5266_)) as u8;
                                        if v_isSharedCheck_5284_ == 0 {
                                            v___x_5279_ = v___x_5266_;
                                            v_isShared_5280_ = v_isSharedCheck_5284_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5277_);
                                            leanh::lean_dec(v___x_5266_);
                                            v___x_5279_ = leanh::lean_box(0);
                                            v_isShared_5280_ = v_isSharedCheck_5284_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5285_ = leanh::lean_ctor_get(v___x_5266_, 0);
                                        leanh::lean_inc(v_a_5285_);
                                        leanh::lean_dec_ref_known(v___x_5266_, 1);
                                        v___x_5286_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10;
                                        leanh::lean_inc(v_json_5222_);
                                        v___x_5287_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_5222_, v___x_5286_);
                                        if leanh::lean_obj_tag(v___x_5287_) == 0 {
                                            leanh::lean_dec(v_a_5285_);
                                            leanh::lean_dec(v_a_5264_);
                                            leanh::lean_dec(v_a_5243_);
                                            leanh::lean_dec(v_json_5222_);
                                            v_a_5288_ = leanh::lean_ctor_get(v___x_5287_, 0);
                                            v_isSharedCheck_5297_ =
                                                (!leanh::lean_is_exclusive(v___x_5287_))
                                                    as u8;
                                            if v_isSharedCheck_5297_ == 0 {
                                                v___x_5290_ = v___x_5287_;
                                                v_isShared_5291_ = v_isSharedCheck_5297_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_5288_);
                                                leanh::lean_dec(v___x_5287_);
                                                v___x_5290_ = leanh::lean_box(0);
                                                v_isShared_5291_ = v_isSharedCheck_5297_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_5287_) == 0 {
                                                leanh::lean_dec(v_a_5285_);
                                                leanh::lean_dec(v_a_5264_);
                                                leanh::lean_dec(v_a_5243_);
                                                leanh::lean_dec(v_json_5222_);
                                                v_a_5298_ =
                                                    leanh::lean_ctor_get(v___x_5287_, 0);
                                                v_isSharedCheck_5305_ =
                                                    (!leanh::lean_is_exclusive(v___x_5287_))
                                                        as u8;
                                                if v_isSharedCheck_5305_ == 0 {
                                                    v___x_5300_ = v___x_5287_;
                                                    v_isShared_5301_ = v_isSharedCheck_5305_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_5298_);
                                                    leanh::lean_dec(v___x_5287_);
                                                    v___x_5300_ = leanh::lean_box(0);
                                                    v_isShared_5301_ = v_isSharedCheck_5305_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5306_ =
                                                    leanh::lean_ctor_get(v___x_5287_, 0);
                                                leanh::lean_inc(v_a_5306_);
                                                leanh::lean_dec_ref_known(v___x_5287_, 1);
                                                v___x_5307_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11;
                                                leanh::lean_inc(v_json_5222_);
                                                v___x_5308_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_json_5222_, v___x_5307_);
                                                if leanh::lean_obj_tag(v___x_5308_) == 0 {
                                                    leanh::lean_dec(v_a_5306_);
                                                    leanh::lean_dec(v_a_5285_);
                                                    leanh::lean_dec(v_a_5264_);
                                                    leanh::lean_dec(v_a_5243_);
                                                    leanh::lean_dec(v_json_5222_);
                                                    v_a_5309_ =
                                                        leanh::lean_ctor_get(v___x_5308_, 0);
                                                    v_isSharedCheck_5318_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_5308_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5318_ == 0 {
                                                        v___x_5311_ = v___x_5308_;
                                                        v_isShared_5312_ = v_isSharedCheck_5318_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_5309_);
                                                        leanh::lean_dec(v___x_5308_);
                                                        v___x_5311_ = leanh::lean_box(0);
                                                        v_isShared_5312_ = v_isSharedCheck_5318_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if leanh::lean_obj_tag(v___x_5308_) == 0
                                                    {
                                                        leanh::lean_dec(v_a_5306_);
                                                        leanh::lean_dec(v_a_5285_);
                                                        leanh::lean_dec(v_a_5264_);
                                                        leanh::lean_dec(v_a_5243_);
                                                        leanh::lean_dec(v_json_5222_);
                                                        v_a_5319_ = leanh::lean_ctor_get(
                                                            v___x_5308_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_5326_ =
                                                            (!leanh::lean_is_exclusive(
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
                                                            leanh::lean_inc(v_a_5319_);
                                                            leanh::lean_dec(v___x_5308_);
                                                            v___x_5321_ = leanh::lean_box(0);
                                                            v_isShared_5322_ =
                                                                v_isSharedCheck_5326_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_5327_ = leanh::lean_ctor_get(
                                                            v___x_5308_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_5327_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_5308_,
                                                            1,
                                                        );
                                                        v___x_5328_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12;
                                                        leanh::lean_inc(v_json_5222_);
                                                        v___x_5329_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_json_5222_, v___x_5328_);
                                                        if leanh::lean_obj_tag(v___x_5329_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec(v_a_5327_);
                                                            leanh::lean_dec(v_a_5306_);
                                                            leanh::lean_dec(v_a_5285_);
                                                            leanh::lean_dec(v_a_5264_);
                                                            leanh::lean_dec(v_a_5243_);
                                                            leanh::lean_dec(v_json_5222_);
                                                            v_a_5330_ = leanh::lean_ctor_get(
                                                                v___x_5329_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5339_ =
                                                                (!leanh::lean_is_exclusive(
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
                                                                leanh::lean_inc(v_a_5330_);
                                                                leanh::lean_dec(v___x_5329_);
                                                                v___x_5332_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_5333_ =
                                                                    v_isSharedCheck_5339_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if leanh::lean_obj_tag(
                                                                v___x_5329_,
                                                            ) == 0
                                                            {
                                                                leanh::lean_dec(v_a_5327_);
                                                                leanh::lean_dec(v_a_5306_);
                                                                leanh::lean_dec(v_a_5285_);
                                                                leanh::lean_dec(v_a_5264_);
                                                                leanh::lean_dec(v_a_5243_);
                                                                leanh::lean_dec(
                                                                    v_json_5222_,
                                                                );
                                                                v_a_5340_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_5329_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_5347_ = (!leanh::lean_is_exclusive(v___x_5329_)) as u8;
                                                                if v_isSharedCheck_5347_ == 0 {
                                                                    v___x_5342_ = v___x_5329_;
                                                                    v_isShared_5343_ =
                                                                        v_isSharedCheck_5347_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_5340_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_5329_,
                                                                    );
                                                                    v___x_5342_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_5343_ =
                                                                        v_isSharedCheck_5347_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_5348_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_5329_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_a_5348_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_5329_,
                                                                    1,
                                                                );
                                                                v___x_5349_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1;
                                                                leanh::lean_inc(
                                                                    v_json_5222_,
                                                                );
                                                                v___x_5350_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_5222_, v___x_5349_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_5350_,
                                                                ) == 0
                                                                {
                                                                    leanh::lean_dec(
                                                                        v_a_5348_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5327_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5306_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5285_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5264_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_5243_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_json_5222_,
                                                                    );
                                                                    v_a_5351_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_5350_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_5360_ = (!leanh::lean_is_exclusive(v___x_5350_)) as u8;
                                                                    if v_isSharedCheck_5360_ == 0 {
                                                                        v___x_5353_ = v___x_5350_;
                                                                        v_isShared_5354_ =
                                                                            v_isSharedCheck_5360_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_5351_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_5350_,
                                                                        );
                                                                        v___x_5353_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_5354_ =
                                                                            v_isSharedCheck_5360_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_5350_,
                                                                    ) == 0
                                                                    {
                                                                        leanh::lean_dec(
                                                                            v_a_5348_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5327_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5306_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5285_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5264_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_5243_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_json_5222_,
                                                                        );
                                                                        v_a_5361_ = leanh::lean_ctor_get(v___x_5350_, 0);
                                                                        v_isSharedCheck_5368_ = (!leanh::lean_is_exclusive(v___x_5350_)) as u8;
                                                                        if v_isSharedCheck_5368_
                                                                            == 0
                                                                        {
                                                                            v___x_5363_ =
                                                                                v___x_5350_;
                                                                            v_isShared_5364_ = v_isSharedCheck_5368_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_5361_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_5350_,
                                                                            );
                                                                            v___x_5363_ = leanh::lean_box(0);
                                                                            v_isShared_5364_ = v_isSharedCheck_5368_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_5369_ = leanh::lean_ctor_get(v___x_5350_, 0);
                                                                        leanh::lean_inc(
                                                                            v_a_5369_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v___x_5350_, 1);
                                                                        v___x_5370_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13;
                                                                        leanh::lean_inc(
                                                                            v_json_5222_,
                                                                        );
                                                                        v___x_5371_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_json_5222_, v___x_5370_);
                                                                        if leanh::lean_obj_tag(v___x_5371_) == 0 {
leanh::lean_dec(v_a_5369_);
leanh::lean_dec(v_a_5348_);
leanh::lean_dec(v_a_5327_);
leanh::lean_dec(v_a_5306_);
leanh::lean_dec(v_a_5285_);
leanh::lean_dec(v_a_5264_);
leanh::lean_dec(v_a_5243_);
leanh::lean_dec(v_json_5222_);
v_a_5372_ = leanh::lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5381_ = (!leanh::lean_is_exclusive(v___x_5371_)) as u8;
if v_isSharedCheck_5381_ == 0 {
v___x_5374_ = v___x_5371_;
v_isShared_5375_ = v_isSharedCheck_5381_;
state = 29; continue;
} else {
leanh::lean_inc(v_a_5372_);
leanh::lean_dec(v___x_5371_);
v___x_5374_ = leanh::lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5381_;
state = 29; continue;
}
} else {
if leanh::lean_obj_tag(v___x_5371_) == 0 {
leanh::lean_dec(v_a_5369_);
leanh::lean_dec(v_a_5348_);
leanh::lean_dec(v_a_5327_);
leanh::lean_dec(v_a_5306_);
leanh::lean_dec(v_a_5285_);
leanh::lean_dec(v_a_5264_);
leanh::lean_dec(v_a_5243_);
leanh::lean_dec(v_json_5222_);
v_a_5382_ = leanh::lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5389_ = (!leanh::lean_is_exclusive(v___x_5371_)) as u8;
if v_isSharedCheck_5389_ == 0 {
v___x_5384_ = v___x_5371_;
v_isShared_5385_ = v_isSharedCheck_5389_;
state = 31; continue;
} else {
leanh::lean_inc(v_a_5382_);
leanh::lean_dec(v___x_5371_);
v___x_5384_ = leanh::lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
state = 31; continue;
}
} else {
v_a_5390_ = leanh::lean_ctor_get(v___x_5371_, 0);
leanh::lean_inc(v_a_5390_);
leanh::lean_dec_ref_known(v___x_5371_, 1);
v___x_5391_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14;
leanh::lean_inc(v_json_5222_);
v___x_5392_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_json_5222_, v___x_5391_);
if leanh::lean_obj_tag(v___x_5392_) == 0 {
leanh::lean_dec(v_a_5390_);
leanh::lean_dec(v_a_5369_);
leanh::lean_dec(v_a_5348_);
leanh::lean_dec(v_a_5327_);
leanh::lean_dec(v_a_5306_);
leanh::lean_dec(v_a_5285_);
leanh::lean_dec(v_a_5264_);
leanh::lean_dec(v_a_5243_);
leanh::lean_dec(v_json_5222_);
v_a_5393_ = leanh::lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5402_ = (!leanh::lean_is_exclusive(v___x_5392_)) as u8;
if v_isSharedCheck_5402_ == 0 {
v___x_5395_ = v___x_5392_;
v_isShared_5396_ = v_isSharedCheck_5402_;
state = 33; continue;
} else {
leanh::lean_inc(v_a_5393_);
leanh::lean_dec(v___x_5392_);
v___x_5395_ = leanh::lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5402_;
state = 33; continue;
}
} else {
if leanh::lean_obj_tag(v___x_5392_) == 0 {
leanh::lean_dec(v_a_5390_);
leanh::lean_dec(v_a_5369_);
leanh::lean_dec(v_a_5348_);
leanh::lean_dec(v_a_5327_);
leanh::lean_dec(v_a_5306_);
leanh::lean_dec(v_a_5285_);
leanh::lean_dec(v_a_5264_);
leanh::lean_dec(v_a_5243_);
leanh::lean_dec(v_json_5222_);
v_a_5403_ = leanh::lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5410_ = (!leanh::lean_is_exclusive(v___x_5392_)) as u8;
if v_isSharedCheck_5410_ == 0 {
v___x_5405_ = v___x_5392_;
v_isShared_5406_ = v_isSharedCheck_5410_;
state = 35; continue;
} else {
leanh::lean_inc(v_a_5403_);
leanh::lean_dec(v___x_5392_);
v___x_5405_ = leanh::lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
state = 35; continue;
}
} else {
v_a_5411_ = leanh::lean_ctor_get(v___x_5392_, 0);
leanh::lean_inc(v_a_5411_);
leanh::lean_dec_ref_known(v___x_5392_, 1);
v___x_5412_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15;
leanh::lean_inc(v_json_5222_);
v___x_5413_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_json_5222_, v___x_5412_);
if leanh::lean_obj_tag(v___x_5413_) == 0 {
leanh::lean_dec(v_a_5411_);
leanh::lean_dec(v_a_5390_);
leanh::lean_dec(v_a_5369_);
leanh::lean_dec(v_a_5348_);
leanh::lean_dec(v_a_5327_);
leanh::lean_dec(v_a_5306_);
leanh::lean_dec(v_a_5285_);
leanh::lean_dec(v_a_5264_);
leanh::lean_dec(v_a_5243_);
leanh::lean_dec(v_json_5222_);
v_a_5414_ = leanh::lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5423_ = (!leanh::lean_is_exclusive(v___x_5413_)) as u8;
if v_isSharedCheck_5423_ == 0 {
v___x_5416_ = v___x_5413_;
v_isShared_5417_ = v_isSharedCheck_5423_;
state = 37; continue;
} else {
leanh::lean_inc(v_a_5414_);
leanh::lean_dec(v___x_5413_);
v___x_5416_ = leanh::lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5423_;
state = 37; continue;
}
} else {
if leanh::lean_obj_tag(v___x_5413_) == 0 {
leanh::lean_dec(v_a_5411_);
leanh::lean_dec(v_a_5390_);
leanh::lean_dec(v_a_5369_);
leanh::lean_dec(v_a_5348_);
leanh::lean_dec(v_a_5327_);
leanh::lean_dec(v_a_5306_);
leanh::lean_dec(v_a_5285_);
leanh::lean_dec(v_a_5264_);
leanh::lean_dec(v_a_5243_);
leanh::lean_dec(v_json_5222_);
v_a_5424_ = leanh::lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5431_ = (!leanh::lean_is_exclusive(v___x_5413_)) as u8;
if v_isSharedCheck_5431_ == 0 {
v___x_5426_ = v___x_5413_;
v_isShared_5427_ = v_isSharedCheck_5431_;
state = 39; continue;
} else {
leanh::lean_inc(v_a_5424_);
leanh::lean_dec(v___x_5413_);
v___x_5426_ = leanh::lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
state = 39; continue;
}
} else {
v_a_5432_ = leanh::lean_ctor_get(v___x_5413_, 0);
leanh::lean_inc(v_a_5432_);
leanh::lean_dec_ref_known(v___x_5413_, 1);
v___x_5433_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16;
v___x_5434_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_json_5222_, v___x_5433_);
v_a_5435_ = leanh::lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5443_ = (!leanh::lean_is_exclusive(v___x_5434_)) as u8;
if v_isSharedCheck_5443_ == 0 {
v___x_5437_ = v___x_5434_;
v_isShared_5438_ = v_isSharedCheck_5443_;
state = 41; continue;
} else {
leanh::lean_inc(v_a_5435_);
leanh::lean_dec(v___x_5434_);
v___x_5437_ = leanh::lean_box(0);
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
                v___x_5229_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9,
                );
                v___x_5230_ = lean_string_append(v___x_5229_, v_a_5225_);
                leanh::lean_dec(v_a_5225_);
                if v_isShared_5228_ == 0 {
                    leanh::lean_ctor_set(v___x_5227_, 0, v___x_5230_);
                    v___x_5232_ = v___x_5227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5233_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5230_);
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
                    leanh::lean_ctor_set_tag(v___x_5237_, 0);
                    v___x_5240_ = v___x_5237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5241_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
                    v___x_5240_ = v_reuseFailAlloc_5241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5240_;
            }
            5 => {
                v___x_5250_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14,
                );
                v___x_5251_ = lean_string_append(v___x_5250_, v_a_5246_);
                leanh::lean_dec(v_a_5246_);
                if v_isShared_5249_ == 0 {
                    leanh::lean_ctor_set(v___x_5248_, 0, v___x_5251_);
                    v___x_5253_ = v___x_5248_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5251_);
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
                    leanh::lean_ctor_set_tag(v___x_5258_, 0);
                    v___x_5261_ = v___x_5258_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
                    v___x_5261_ = v_reuseFailAlloc_5262_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5261_;
            }
            9 => {
                v___x_5271_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20,
                );
                v___x_5272_ = lean_string_append(v___x_5271_, v_a_5267_);
                leanh::lean_dec(v_a_5267_);
                if v_isShared_5270_ == 0 {
                    leanh::lean_ctor_set(v___x_5269_, 0, v___x_5272_);
                    v___x_5274_ = v___x_5269_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5275_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5272_);
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
                    leanh::lean_ctor_set_tag(v___x_5279_, 0);
                    v___x_5282_ = v___x_5279_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
                    v___x_5282_ = v_reuseFailAlloc_5283_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5282_;
            }
            13 => {
                v___x_5292_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27,
                );
                v___x_5293_ = lean_string_append(v___x_5292_, v_a_5288_);
                leanh::lean_dec(v_a_5288_);
                if v_isShared_5291_ == 0 {
                    leanh::lean_ctor_set(v___x_5290_, 0, v___x_5293_);
                    v___x_5295_ = v___x_5290_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5296_, 0, v___x_5293_);
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
                    leanh::lean_ctor_set_tag(v___x_5300_, 0);
                    v___x_5303_ = v___x_5300_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
                    v___x_5303_ = v_reuseFailAlloc_5304_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5303_;
            }
            17 => {
                v___x_5313_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33,
                );
                v___x_5314_ = lean_string_append(v___x_5313_, v_a_5309_);
                leanh::lean_dec(v_a_5309_);
                if v_isShared_5312_ == 0 {
                    leanh::lean_ctor_set(v___x_5311_, 0, v___x_5314_);
                    v___x_5316_ = v___x_5311_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5317_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5317_, 0, v___x_5314_);
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
                    leanh::lean_ctor_set_tag(v___x_5321_, 0);
                    v___x_5324_ = v___x_5321_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5325_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
                    v___x_5324_ = v_reuseFailAlloc_5325_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5324_;
            }
            21 => {
                v___x_5334_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40,
                );
                v___x_5335_ = lean_string_append(v___x_5334_, v_a_5330_);
                leanh::lean_dec(v_a_5330_);
                if v_isShared_5333_ == 0 {
                    leanh::lean_ctor_set(v___x_5332_, 0, v___x_5335_);
                    v___x_5337_ = v___x_5332_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5338_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5338_, 0, v___x_5335_);
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
                    leanh::lean_ctor_set_tag(v___x_5342_, 0);
                    v___x_5345_ = v___x_5342_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5346_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
                    v___x_5345_ = v_reuseFailAlloc_5346_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5345_;
            }
            25 => {
                v___x_5355_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42,
                );
                v___x_5356_ = lean_string_append(v___x_5355_, v_a_5351_);
                leanh::lean_dec(v_a_5351_);
                if v_isShared_5354_ == 0 {
                    leanh::lean_ctor_set(v___x_5353_, 0, v___x_5356_);
                    v___x_5358_ = v___x_5353_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5356_);
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
                    leanh::lean_ctor_set_tag(v___x_5363_, 0);
                    v___x_5366_ = v___x_5363_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5367_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
                    v___x_5366_ = v_reuseFailAlloc_5367_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5366_;
            }
            29 => {
                v___x_5376_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49,
                );
                v___x_5377_ = lean_string_append(v___x_5376_, v_a_5372_);
                leanh::lean_dec(v_a_5372_);
                if v_isShared_5375_ == 0 {
                    leanh::lean_ctor_set(v___x_5374_, 0, v___x_5377_);
                    v___x_5379_ = v___x_5374_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5380_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5377_);
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
                    leanh::lean_ctor_set_tag(v___x_5384_, 0);
                    v___x_5387_ = v___x_5384_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5388_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
                    v___x_5387_ = v_reuseFailAlloc_5388_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5387_;
            }
            33 => {
                v___x_5397_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56,
                );
                v___x_5398_ = lean_string_append(v___x_5397_, v_a_5393_);
                leanh::lean_dec(v_a_5393_);
                if v_isShared_5396_ == 0 {
                    leanh::lean_ctor_set(v___x_5395_, 0, v___x_5398_);
                    v___x_5400_ = v___x_5395_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
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
                    leanh::lean_ctor_set_tag(v___x_5405_, 0);
                    v___x_5408_ = v___x_5405_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
                    v___x_5408_ = v_reuseFailAlloc_5409_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5408_;
            }
            37 => {
                v___x_5418_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63,
                );
                v___x_5419_ = lean_string_append(v___x_5418_, v_a_5414_);
                leanh::lean_dec(v_a_5414_);
                if v_isShared_5417_ == 0 {
                    leanh::lean_ctor_set(v___x_5416_, 0, v___x_5419_);
                    v___x_5421_ = v___x_5416_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5422_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5419_);
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
                    leanh::lean_ctor_set_tag(v___x_5426_, 0);
                    v___x_5429_ = v___x_5426_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5430_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
                    v___x_5429_ = v_reuseFailAlloc_5430_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5429_;
            }
            41 => {
                v___x_5439_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                leanh::lean_ctor_set(v___x_5439_, 0, v_a_5243_);
                leanh::lean_ctor_set(v___x_5439_, 1, v_a_5264_);
                leanh::lean_ctor_set(v___x_5439_, 2, v_a_5285_);
                leanh::lean_ctor_set(v___x_5439_, 3, v_a_5306_);
                leanh::lean_ctor_set(v___x_5439_, 4, v_a_5327_);
                leanh::lean_ctor_set(v___x_5439_, 5, v_a_5348_);
                leanh::lean_ctor_set(v___x_5439_, 6, v_a_5369_);
                leanh::lean_ctor_set(v___x_5439_, 7, v_a_5390_);
                leanh::lean_ctor_set(v___x_5439_, 8, v_a_5411_);
                leanh::lean_ctor_set(v___x_5439_, 9, v_a_5432_);
                leanh::lean_ctor_set(v___x_5439_, 10, v_a_5435_);
                if v_isShared_5438_ == 0 {
                    leanh::lean_ctor_set(v___x_5437_, 0, v___x_5439_);
                    v___x_5441_ = v___x_5437_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_5442_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5442_, 0, v___x_5439_);
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
    mut v_bs_5446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5447_: u8 = 0;
    let mut v___x_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v_a_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: usize = 0;
    let mut v___x_5463_: usize = 0;
    let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5447_ = lean_usize_dec_lt(v_i_5445_, v_sz_5444_);
                if v___x_5447_ == 0 {
                    v___x_5448_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5448_, 0, v_bs_5446_);
                    return v___x_5448_;
                } else {
                    v_v_5449_ = lean_array_uget_borrowed(v_bs_5446_, v_i_5445_);
                    leanh::lean_inc(v_v_5449_);
                    v___x_5450_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(v_v_5449_);
                    if leanh::lean_obj_tag(v___x_5450_) == 0 {
                        leanh::lean_dec_ref(v_bs_5446_);
                        v_a_5451_ = leanh::lean_ctor_get(v___x_5450_, 0);
                        v_isSharedCheck_5458_ =
                            (!leanh::lean_is_exclusive(v___x_5450_)) as u8;
                        if v_isSharedCheck_5458_ == 0 {
                            v___x_5453_ = v___x_5450_;
                            v_isShared_5454_ = v_isSharedCheck_5458_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5451_);
                            leanh::lean_dec(v___x_5450_);
                            v___x_5453_ = leanh::lean_box(0);
                            v_isShared_5454_ = v_isSharedCheck_5458_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5459_ = leanh::lean_ctor_get(v___x_5450_, 0);
                        leanh::lean_inc(v_a_5459_);
                        leanh::lean_dec_ref_known(v___x_5450_, 1);
                        v___x_5460_ = leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_5457_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_a_5451_);
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
    mut v_sz_5466_: *mut leanh::LeanObject,
    mut v_i_5467_: *mut leanh::LeanObject,
    mut v_bs_5468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5469_: usize = 0;
    let mut v_i_boxed_5470_: usize = 0;
    let mut v_res_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5469_ = leanh::lean_unbox_usize(v_sz_5466_);
    leanh::lean_dec(v_sz_5466_);
    v_i_boxed_5470_ = leanh::lean_unbox_usize(v_i_5467_);
    leanh::lean_dec(v_i_5467_);
    v_res_5471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_boxed_5469_, v_i_boxed_5470_, v_bs_5468_);
    return v_res_5471_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(
    mut v_x_5472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5472_) == 4 {
        let mut v_elems_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5474_: usize = 0;
        let mut v___x_5475_: usize = 0;
        let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_5473_ = leanh::lean_ctor_get(v_x_5472_, 0);
        leanh::lean_inc_ref(v_elems_5473_);
        leanh::lean_dec_ref_known(v_x_5472_, 1);
        v_sz_5474_ = lean_array_size(v_elems_5473_);
        v___x_5475_ = 0usize;
        v___x_5476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_5474_, v___x_5475_, v_elems_5473_);
        return v___x_5476_;
    } else {
        let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5477_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0;
        v___x_5478_ = leanh::lean_unsigned_to_nat(80);
        v___x_5479_ = l_Lean_Json_pretty(v_x_5472_, v___x_5478_);
        v___x_5480_ = lean_string_append(v___x_5477_, v___x_5479_);
        leanh::lean_dec_ref(v___x_5479_);
        v___x_5481_ = l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1;
        v___x_5482_ = lean_string_append(v___x_5480_, v___x_5481_);
        v___x_5483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5483_, 0, v___x_5482_);
        return v___x_5483_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(
    mut v_j_5484_: *mut leanh::LeanObject,
    mut v_k_5485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5486_ = l_Lean_Json_getObjValD(v_j_5484_, v_k_5485_);
    v___x_5487_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(v___x_5486_);
    return v___x_5487_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2___boxed(
    mut v_j_5488_: *mut leanh::LeanObject,
    mut v_k_5489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5490_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_j_5488_, v_k_5489_);
    leanh::lean_dec_ref(v_k_5489_);
    return v_res_5490_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5496_: u8 = 0;
    let mut v___x_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5496_ = 1;
    v___x_5497_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1;
    v___x_5498_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5497_, v___x_5496_);
    return v___x_5498_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5499_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5;
    v___x_5500_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_5504_: u8 = 0;
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5504_ = 1;
    v___x_5505_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4;
    v___x_5506_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5505_, v___x_5504_);
    return v___x_5506_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5507_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5,
    );
    v___x_5508_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5510_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_5511_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_5516_: u8 = 0;
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5516_ = 1;
    v___x_5517_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9;
    v___x_5518_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5517_, v___x_5516_);
    return v___x_5518_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5519_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10,
    );
    v___x_5520_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5522_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_5523_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_5528_: u8 = 0;
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5528_ = 1;
    v___x_5529_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14;
    v___x_5530_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5529_, v___x_5528_);
    return v___x_5530_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5531_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15,
    );
    v___x_5532_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5534_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_5535_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_5539_: u8 = 0;
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5539_ = 1;
    v___x_5540_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18;
    v___x_5541_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5540_, v___x_5539_);
    return v___x_5541_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5542_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once
        ),
        _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19,
    );
    v___x_5543_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5545_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10;
    v___x_5546_ = leanh::lean_obj_once(
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
    mut v_json_5548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5554_: u8 = 0;
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5560_: u8 = 0;
    let mut v_a_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5564_: u8 = 0;
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5568_: u8 = 0;
    let mut v_a_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5575_: u8 = 0;
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut v_a_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5585_: u8 = 0;
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_a_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5596_: u8 = 0;
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v_a_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5606_: u8 = 0;
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5610_: u8 = 0;
    let mut v_a_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5623_: u8 = 0;
    let mut v_a_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5627_: u8 = 0;
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5631_: u8 = 0;
    let mut v_a_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5635_: u8 = 0;
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5549_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0;
                leanh::lean_inc(v_json_5548_);
                v___x_5550_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_5548_, v___x_5549_);
                if leanh::lean_obj_tag(v___x_5550_) == 0 {
                    leanh::lean_dec(v_json_5548_);
                    v_a_5551_ = leanh::lean_ctor_get(v___x_5550_, 0);
                    v_isSharedCheck_5560_ = (!leanh::lean_is_exclusive(v___x_5550_)) as u8;
                    if v_isSharedCheck_5560_ == 0 {
                        v___x_5553_ = v___x_5550_;
                        v_isShared_5554_ = v_isSharedCheck_5560_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5551_);
                        leanh::lean_dec(v___x_5550_);
                        v___x_5553_ = leanh::lean_box(0);
                        v_isShared_5554_ = v_isSharedCheck_5560_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_5550_) == 0 {
                        leanh::lean_dec(v_json_5548_);
                        v_a_5561_ = leanh::lean_ctor_get(v___x_5550_, 0);
                        v_isSharedCheck_5568_ =
                            (!leanh::lean_is_exclusive(v___x_5550_)) as u8;
                        if v_isSharedCheck_5568_ == 0 {
                            v___x_5563_ = v___x_5550_;
                            v_isShared_5564_ = v_isSharedCheck_5568_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5561_);
                            leanh::lean_dec(v___x_5550_);
                            v___x_5563_ = leanh::lean_box(0);
                            v_isShared_5564_ = v_isSharedCheck_5568_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5569_ = leanh::lean_ctor_get(v___x_5550_, 0);
                        leanh::lean_inc(v_a_5569_);
                        leanh::lean_dec_ref_known(v___x_5550_, 1);
                        v___x_5570_ =
                            l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1;
                        leanh::lean_inc(v_json_5548_);
                        v___x_5571_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_json_5548_, v___x_5570_);
                        if leanh::lean_obj_tag(v___x_5571_) == 0 {
                            leanh::lean_dec(v_a_5569_);
                            leanh::lean_dec(v_json_5548_);
                            v_a_5572_ = leanh::lean_ctor_get(v___x_5571_, 0);
                            v_isSharedCheck_5581_ =
                                (!leanh::lean_is_exclusive(v___x_5571_)) as u8;
                            if v_isSharedCheck_5581_ == 0 {
                                v___x_5574_ = v___x_5571_;
                                v_isShared_5575_ = v_isSharedCheck_5581_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5572_);
                                leanh::lean_dec(v___x_5571_);
                                v___x_5574_ = leanh::lean_box(0);
                                v_isShared_5575_ = v_isSharedCheck_5581_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_5571_) == 0 {
                                leanh::lean_dec(v_a_5569_);
                                leanh::lean_dec(v_json_5548_);
                                v_a_5582_ = leanh::lean_ctor_get(v___x_5571_, 0);
                                v_isSharedCheck_5589_ =
                                    (!leanh::lean_is_exclusive(v___x_5571_)) as u8;
                                if v_isSharedCheck_5589_ == 0 {
                                    v___x_5584_ = v___x_5571_;
                                    v_isShared_5585_ = v_isSharedCheck_5589_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5582_);
                                    leanh::lean_dec(v___x_5571_);
                                    v___x_5584_ = leanh::lean_box(0);
                                    v_isShared_5585_ = v_isSharedCheck_5589_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5590_ = leanh::lean_ctor_get(v___x_5571_, 0);
                                leanh::lean_inc(v_a_5590_);
                                leanh::lean_dec_ref_known(v___x_5571_, 1);
                                v___x_5591_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2;
                                leanh::lean_inc(v_json_5548_);
                                v___x_5592_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_5548_, v___x_5591_);
                                if leanh::lean_obj_tag(v___x_5592_) == 0 {
                                    leanh::lean_dec(v_a_5590_);
                                    leanh::lean_dec(v_a_5569_);
                                    leanh::lean_dec(v_json_5548_);
                                    v_a_5593_ = leanh::lean_ctor_get(v___x_5592_, 0);
                                    v_isSharedCheck_5602_ =
                                        (!leanh::lean_is_exclusive(v___x_5592_)) as u8;
                                    if v_isSharedCheck_5602_ == 0 {
                                        v___x_5595_ = v___x_5592_;
                                        v_isShared_5596_ = v_isSharedCheck_5602_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5593_);
                                        leanh::lean_dec(v___x_5592_);
                                        v___x_5595_ = leanh::lean_box(0);
                                        v_isShared_5596_ = v_isSharedCheck_5602_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v___x_5592_) == 0 {
                                        leanh::lean_dec(v_a_5590_);
                                        leanh::lean_dec(v_a_5569_);
                                        leanh::lean_dec(v_json_5548_);
                                        v_a_5603_ = leanh::lean_ctor_get(v___x_5592_, 0);
                                        v_isSharedCheck_5610_ =
                                            (!leanh::lean_is_exclusive(v___x_5592_)) as u8;
                                        if v_isSharedCheck_5610_ == 0 {
                                            v___x_5605_ = v___x_5592_;
                                            v_isShared_5606_ = v_isSharedCheck_5610_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5603_);
                                            leanh::lean_dec(v___x_5592_);
                                            v___x_5605_ = leanh::lean_box(0);
                                            v_isShared_5606_ = v_isSharedCheck_5610_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5611_ = leanh::lean_ctor_get(v___x_5592_, 0);
                                        leanh::lean_inc(v_a_5611_);
                                        leanh::lean_dec_ref_known(v___x_5592_, 1);
                                        v___x_5612_ = l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3;
                                        v___x_5613_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_json_5548_, v___x_5612_);
                                        if leanh::lean_obj_tag(v___x_5613_) == 0 {
                                            leanh::lean_dec(v_a_5611_);
                                            leanh::lean_dec(v_a_5590_);
                                            leanh::lean_dec(v_a_5569_);
                                            v_a_5614_ = leanh::lean_ctor_get(v___x_5613_, 0);
                                            v_isSharedCheck_5623_ =
                                                (!leanh::lean_is_exclusive(v___x_5613_))
                                                    as u8;
                                            if v_isSharedCheck_5623_ == 0 {
                                                v___x_5616_ = v___x_5613_;
                                                v_isShared_5617_ = v_isSharedCheck_5623_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_5614_);
                                                leanh::lean_dec(v___x_5613_);
                                                v___x_5616_ = leanh::lean_box(0);
                                                v_isShared_5617_ = v_isSharedCheck_5623_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_5613_) == 0 {
                                                leanh::lean_dec(v_a_5611_);
                                                leanh::lean_dec(v_a_5590_);
                                                leanh::lean_dec(v_a_5569_);
                                                v_a_5624_ =
                                                    leanh::lean_ctor_get(v___x_5613_, 0);
                                                v_isSharedCheck_5631_ =
                                                    (!leanh::lean_is_exclusive(v___x_5613_))
                                                        as u8;
                                                if v_isSharedCheck_5631_ == 0 {
                                                    v___x_5626_ = v___x_5613_;
                                                    v_isShared_5627_ = v_isSharedCheck_5631_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_5624_);
                                                    leanh::lean_dec(v___x_5613_);
                                                    v___x_5626_ = leanh::lean_box(0);
                                                    v_isShared_5627_ = v_isSharedCheck_5631_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5632_ =
                                                    leanh::lean_ctor_get(v___x_5613_, 0);
                                                v_isSharedCheck_5640_ =
                                                    (!leanh::lean_is_exclusive(v___x_5613_))
                                                        as u8;
                                                if v_isSharedCheck_5640_ == 0 {
                                                    v___x_5634_ = v___x_5613_;
                                                    v_isShared_5635_ = v_isSharedCheck_5640_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_5632_);
                                                    leanh::lean_dec(v___x_5613_);
                                                    v___x_5634_ = leanh::lean_box(0);
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
                v___x_5555_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7,
                );
                v___x_5556_ = lean_string_append(v___x_5555_, v_a_5551_);
                leanh::lean_dec(v_a_5551_);
                if v_isShared_5554_ == 0 {
                    leanh::lean_ctor_set(v___x_5553_, 0, v___x_5556_);
                    v___x_5558_ = v___x_5553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5559_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5556_);
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
                    leanh::lean_ctor_set_tag(v___x_5563_, 0);
                    v___x_5566_ = v___x_5563_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5567_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
                    v___x_5566_ = v_reuseFailAlloc_5567_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5566_;
            }
            5 => {
                v___x_5576_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12,
                );
                v___x_5577_ = lean_string_append(v___x_5576_, v_a_5572_);
                leanh::lean_dec(v_a_5572_);
                if v_isShared_5575_ == 0 {
                    leanh::lean_ctor_set(v___x_5574_, 0, v___x_5577_);
                    v___x_5579_ = v___x_5574_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5580_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5577_);
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
                    leanh::lean_ctor_set_tag(v___x_5584_, 0);
                    v___x_5587_ = v___x_5584_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5588_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_a_5582_);
                    v___x_5587_ = v_reuseFailAlloc_5588_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5587_;
            }
            9 => {
                v___x_5597_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17,
                );
                v___x_5598_ = lean_string_append(v___x_5597_, v_a_5593_);
                leanh::lean_dec(v_a_5593_);
                if v_isShared_5596_ == 0 {
                    leanh::lean_ctor_set(v___x_5595_, 0, v___x_5598_);
                    v___x_5600_ = v___x_5595_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5601_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5598_);
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
                    leanh::lean_ctor_set_tag(v___x_5605_, 0);
                    v___x_5608_ = v___x_5605_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
                    v___x_5608_ = v_reuseFailAlloc_5609_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5608_;
            }
            13 => {
                v___x_5618_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21,
                );
                v___x_5619_ = lean_string_append(v___x_5618_, v_a_5614_);
                leanh::lean_dec(v_a_5614_);
                if v_isShared_5617_ == 0 {
                    leanh::lean_ctor_set(v___x_5616_, 0, v___x_5619_);
                    v___x_5621_ = v___x_5616_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5622_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5619_);
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
                    leanh::lean_ctor_set_tag(v___x_5626_, 0);
                    v___x_5629_ = v___x_5626_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5630_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
                    v___x_5629_ = v_reuseFailAlloc_5630_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5629_;
            }
            17 => {
                v___x_5636_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5636_, 0, v_a_5569_);
                leanh::lean_ctor_set(v___x_5636_, 1, v_a_5590_);
                leanh::lean_ctor_set(v___x_5636_, 2, v_a_5611_);
                leanh::lean_ctor_set(v___x_5636_, 3, v_a_5632_);
                if v_isShared_5635_ == 0 {
                    leanh::lean_ctor_set(v___x_5634_, 0, v___x_5636_);
                    v___x_5638_ = v___x_5634_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5639_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5636_);
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
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Lsp_instInhabitedDiagnosticSeverity_default =
        _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity_default();
    l_Lean_Lsp_instInhabitedDiagnosticSeverity = _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity();
    l_Lean_Lsp_instInhabitedDiagnosticCode_default =
        _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default();
    leanh::lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticCode_default);
    l_Lean_Lsp_instInhabitedDiagnosticCode = _init_l_Lean_Lsp_instInhabitedDiagnosticCode();
    leanh::lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticCode);
    l_Lean_Lsp_instInhabitedDiagnosticTag_default =
        _init_l_Lean_Lsp_instInhabitedDiagnosticTag_default();
    l_Lean_Lsp_instInhabitedDiagnosticTag = _init_l_Lean_Lsp_instInhabitedDiagnosticTag();
    l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default =
        _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default();
    l_Lean_Lsp_instInhabitedLeanDiagnosticTag = _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag();
    l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default =
        _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default();
    leanh::lean_mark_persistent(
        l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default,
    );
    l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation =
        _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation();
    leanh::lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Diagnostics(
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
pub unsafe fn initialize_Lean_Data_Lsp_Diagnostics(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Utf16(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Diagnostics(builtin);
}