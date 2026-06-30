// Lean compiler output
// Module: Lean.DocString.Links
// Imports: Lean.Syntax Init.Data.String.TakeDrop Init.Data.String.Search Init.Data.ToString.Macro Init.While Init.Data.String.Length
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_io_getenv, lean_manual_get_root, lean_mk_array,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_string_append, lean_string_dec_eq, lean_string_hash, lean_string_memcmp,
    lean_string_push, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_dec_eq,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_String_quote;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Syntax::{initialize_Lean_Syntax, runtime_initialize_Lean_Syntax};
pub static l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0_value:
    leanh::LeanStringObject<44> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        104, 116, 116, 112, 115, 58, 47, 47, 108, 101, 97, 110, 45, 108, 97, 110, 103, 46, 111,
        114, 103, 47, 100, 111, 99, 47, 114, 101, 102, 101, 114, 101, 110, 99, 101, 47, 108, 97,
        116, 101, 115, 116, 47, 0,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [76, 69, 65, 78, 95, 77, 65, 78, 85, 65, 76, 95, 82, 79, 79, 84, 0]};
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_: u8 = 0;
pub static mut l_Lean_manualRoot: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_errorExplanationManualDomain___closed__0_value: leanh::LeanStringObject<
    24,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        77, 97, 110, 117, 97, 108, 46, 101, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97,
        116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_errorExplanationManualDomain___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_errorExplanationManualDomain___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_errorExplanationManualDomain: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_errorExplanationManualDomain___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_domainMap___closed__0_value:
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
    m_data: [115, 101, 99, 116, 105, 111, 110, 0],
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_domainMap___closed__1_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        86, 101, 114, 115, 111, 46, 71, 101, 110, 114, 101, 46, 77, 97, 110, 117, 97, 108, 46, 115,
        101, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_domainMap___closed__2_value:
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
        core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_domainMap___closed__3_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        101, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_domainMap___closed__4_value:
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
        core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_errorExplanationManualDomain___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_domainMap___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__4_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_DocString_Links_0__Lean_domainMap: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_manualDomains: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0_value:
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
static mut l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_manualLink___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
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
            102, 105, 110, 100, 47, 63, 100, 111, 109, 97, 105, 110, 61, 0,
        ],
    };
static mut l_Lean_manualLink___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_manualLink___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_manualLink___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [38, 110, 97, 109, 101, 61, 0],
    };
static mut l_Lean_manualLink___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_manualLink___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_manualLink___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [44, 32, 0],
    };
static mut l_Lean_manualLink___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_manualLink___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_manualLink___closed__3_value: leanh::LeanStringObject<29> =
    leanh::LeanStringObject {
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
            85, 110, 107, 110, 111, 119, 110, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116,
            105, 111, 110, 32, 116, 121, 112, 101, 32, 96, 0,
        ],
    };
static mut l_Lean_manualLink___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_manualLink___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_manualLink___closed__4_value: leanh::LeanStringObject<35> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            96, 46, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 101, 32, 111, 102, 32,
            116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 58, 32, 0,
        ],
    };
static mut l_Lean_manualLink___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_manualLink___closed__4_value) as *mut leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_rw___closed__0_value:
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
        69, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 101, 32, 105, 116, 101, 109, 32, 97,
        102, 116, 101, 114, 32, 96, 0,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_rw___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_rw___closed__1_value:
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
    m_data: [96, 44, 32, 98, 117, 116, 32, 103, 111, 116, 32, 0],
};
static mut l___private_Lean_DocString_Links_0__Lean_rw___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_rw___closed__2_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        77, 105, 115, 115, 105, 110, 103, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105,
        111, 110, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_rw___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_rw___closed__3_value:
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
        core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_DocString_Links_0__Lean_rw___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_rw___closed__4_value:
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
static mut l___private_Lean_DocString_Links_0__Lean_rw___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_rw___closed__5_value:
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
    m_data: [69, 109, 112, 116, 121, 32, 0],
};
static mut l___private_Lean_DocString_Links_0__Lean_rw___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_rw___closed__6_value:
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
    m_data: [32, 73, 68, 0],
};
static mut l___private_Lean_DocString_Links_0__Lean_rw___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Links_0__Lean_rw___closed__7_value:
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
static mut l___private_Lean_DocString_Links_0__Lean_rw___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__7_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [108, 101, 97, 110, 45, 109, 97, 110, 117, 97, 108, 58, 47, 47, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_rewriteManualLinksCore___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_rewriteManualLinksCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rewriteManualLinksCore___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_rewriteManualLinksCore___closed__1_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_rewriteManualLinksCore___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_rewriteManualLinksCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rewriteManualLinksCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_rewriteManualLinksCore___closed__2_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l___private_Lean_DocString_Links_0__Lean_rw___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_rewriteManualLinksCore___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_rewriteManualLinksCore___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rewriteManualLinksCore___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0_value:
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
    m_data: [32, 42, 32, 96, 96, 96, 0],
};
static mut l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1_value:
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
    m_data: [96, 96, 96, 58, 32, 0],
};
static mut l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2_value:
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
    m_data: [10, 10, 0],
};
static mut l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_rewriteManualLinks___closed__0_value: leanh::LeanStringObject<262> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 262,
        m_capacity: 262,
        m_length: 259,
        m_data: [
            42, 42, 226, 157, 140, 32, 83, 121, 110, 116, 97, 120, 32, 69, 114, 114, 111, 114, 115,
            32, 105, 110, 32, 76, 101, 97, 110, 32, 76, 97, 110, 103, 117, 97, 103, 101, 32, 82,
            101, 102, 101, 114, 101, 110, 99, 101, 32, 76, 105, 110, 107, 115, 42, 42, 10, 10, 84,
            104, 101, 32, 96, 108, 101, 97, 110, 45, 109, 97, 110, 117, 97, 108, 96, 32, 85, 82,
            76, 32, 115, 99, 104, 101, 109, 101, 32, 105, 115, 32, 117, 115, 101, 100, 32, 116,
            111, 32, 108, 105, 110, 107, 32, 116, 111, 32, 116, 104, 101, 32, 118, 101, 114, 115,
            105, 111, 110, 32, 111, 102, 32, 116, 104, 101, 32, 76, 101, 97, 110, 32, 114, 101,
            102, 101, 114, 101, 110, 99, 101, 32, 109, 97, 110, 117, 97, 108, 32, 116, 104, 97,
            116, 10, 99, 111, 114, 114, 101, 115, 112, 111, 110, 100, 115, 32, 116, 111, 32, 116,
            104, 105, 115, 32, 118, 101, 114, 115, 105, 111, 110, 32, 111, 102, 32, 76, 101, 97,
            110, 46, 32, 69, 114, 114, 111, 114, 115, 32, 111, 99, 99, 117, 114, 114, 101, 100, 32,
            119, 104, 105, 108, 101, 32, 112, 114, 111, 99, 101, 115, 115, 105, 110, 103, 32, 116,
            104, 101, 32, 108, 105, 110, 107, 115, 32, 105, 110, 32, 116, 104, 105, 115, 32, 100,
            111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 10, 99, 111, 109, 109, 101,
            110, 116, 58, 10, 0,
        ],
    };
static mut l_Lean_rewriteManualLinks___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_rewriteManualLinks___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0_value:
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
    m_data: [32, 42, 32, 0],
};
static mut l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1_value:
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
    m_data: [58, 10, 32, 32, 32, 32, 0],
};
static mut l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2_value:
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
    m_data: [10, 0],
};
static mut l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_validateBuiltinDocString___closed__0_value: leanh::LeanStringObject<42> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            69, 114, 114, 111, 114, 115, 32, 105, 110, 32, 98, 117, 105, 108, 116, 105, 110, 32,
            100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 99, 111, 109, 109,
            101, 110, 116, 58, 10, 0,
        ],
    };
static mut l_Lean_validateBuiltinDocString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_validateBuiltinDocString___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_DocString_Links_0__Lean_getManualRoot___boxed(
    mut v_a_00___x40___internal___hyg_995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_996_ = lean_manual_get_root(v_a_00___x40___internal___hyg_995_);
    return v_res_996_;
}
pub unsafe fn _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1001_ = l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
    v___x_1002_ = lean_string_utf8_byte_size(v___x_1001_);
    return v___x_1002_;
}
pub unsafe fn _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = leanh::lean_box(0);
    v___x_1004_ = lean_manual_get_root(v___x_1003_);
    return v___x_1004_;
}
pub unsafe fn _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1005_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once), _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
    v___x_1006_ = lean_string_utf8_byte_size(v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_()
-> u8 {
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: u8 = 0;
    v___x_1007_ = leanh::lean_unsigned_to_nat(0);
    v___x_1008_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once), _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
    v___x_1009_ = lean_nat_dec_eq(v___x_1008_, v___x_1007_);
    return v___x_1009_;
}
pub unsafe fn l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___y_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: u8 = 0;
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1016_ = l___private_Lean_DocString_Links_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
                v___x_1017_ = lean_io_getenv(v___x_1016_);
                if leanh::lean_obj_tag(v___x_1017_) == 1 {
                    v_val_1028_ = leanh::lean_ctor_get(v___x_1017_, 0);
                    leanh::lean_inc(v_val_1028_);
                    leanh::lean_dec_ref_known(v___x_1017_, 1);
                    v_r_1019_ = v_val_1028_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1017_);
                    v___x_1029_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once), _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
                    v___x_1030_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once), _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
                    if v___x_1030_ == 0 {
                        v_r_1019_ = v___x_1029_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1031_ =
                            l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot___closed__0;
                        v_r_1019_ = v___x_1031_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1014_ = lean_string_append(v___y_1012_, v___y_1013_);
                v___x_1015_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1015_, 0, v___x_1014_);
                return v___x_1015_;
            }
            2 => {
                v___x_1020_ = l___private_Lean_DocString_Links_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_;
                v___x_1021_ = lean_string_utf8_byte_size(v_r_1019_);
                v___x_1022_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2__once), _init_l___private_Lean_DocString_Links_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_);
                v___x_1023_ = lean_nat_dec_le(v___x_1022_, v___x_1021_);
                if v___x_1023_ == 0 {
                    v___y_1012_ = v_r_1019_;
                    v___y_1013_ = v___x_1020_;
                    state = 1;
                    continue;
                } else {
                    v___x_1024_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1025_ = lean_nat_sub(v___x_1021_, v___x_1022_);
                    v___x_1026_ = lean_string_memcmp(
                        v_r_1019_,
                        v___x_1020_,
                        v___x_1025_,
                        v___x_1024_,
                        v___x_1022_,
                    );
                    leanh::lean_dec(v___x_1025_);
                    if v___x_1026_ == 0 {
                        v___y_1012_ = v_r_1019_;
                        v___y_1013_ = v___x_1020_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1027_, 0, v_r_1019_);
                        return v___x_1027_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2____boxed(
    mut v_a_1032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1033_ = l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_();
    return v_res_1033_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_x_1036_: *mut leanh::LeanObject,
    mut v_x_1037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1043_: u8 = 0;
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: u64 = 0;
    let mut v___x_1046_: u64 = 0;
    let mut v___x_1047_: u64 = 0;
    let mut v_fold_1048_: u64 = 0;
    let mut v___x_1049_: u64 = 0;
    let mut v___x_1050_: u64 = 0;
    let mut v___x_1051_: u64 = 0;
    let mut v___x_1052_: usize = 0;
    let mut v___x_1053_: usize = 0;
    let mut v___x_1054_: usize = 0;
    let mut v___x_1055_: usize = 0;
    let mut v___x_1056_: usize = 0;
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1037_) == 0 {
                    return v_x_1036_;
                } else {
                    v_key_1038_ = leanh::lean_ctor_get(v_x_1037_, 0);
                    v_value_1039_ = leanh::lean_ctor_get(v_x_1037_, 1);
                    v_tail_1040_ = leanh::lean_ctor_get(v_x_1037_, 2);
                    v_isSharedCheck_1063_ = (!leanh::lean_is_exclusive(v_x_1037_)) as u8;
                    if v_isSharedCheck_1063_ == 0 {
                        v___x_1042_ = v_x_1037_;
                        v_isShared_1043_ = v_isSharedCheck_1063_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1040_);
                        leanh::lean_inc(v_value_1039_);
                        leanh::lean_inc(v_key_1038_);
                        leanh::lean_dec(v_x_1037_);
                        v___x_1042_ = leanh::lean_box(0);
                        v_isShared_1043_ = v_isSharedCheck_1063_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1044_ = lean_array_get_size(v_x_1036_);
                v___x_1045_ = lean_string_hash(v_key_1038_);
                v___x_1046_ = 32u64;
                v___x_1047_ = lean_uint64_shift_right(v___x_1045_, v___x_1046_);
                v_fold_1048_ = lean_uint64_xor(v___x_1045_, v___x_1047_);
                v___x_1049_ = 16u64;
                v___x_1050_ = lean_uint64_shift_right(v_fold_1048_, v___x_1049_);
                v___x_1051_ = lean_uint64_xor(v_fold_1048_, v___x_1050_);
                v___x_1052_ = lean_uint64_to_usize(v___x_1051_);
                v___x_1053_ = lean_usize_of_nat(v___x_1044_);
                v___x_1054_ = 1usize;
                v___x_1055_ = lean_usize_sub(v___x_1053_, v___x_1054_);
                v___x_1056_ = lean_usize_land(v___x_1052_, v___x_1055_);
                v___x_1057_ = lean_array_uget_borrowed(v_x_1036_, v___x_1056_);
                leanh::lean_inc(v___x_1057_);
                if v_isShared_1043_ == 0 {
                    leanh::lean_ctor_set(v___x_1042_, 2, v___x_1057_);
                    v___x_1059_ = v___x_1042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1062_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_key_1038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_value_1039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1062_, 2, v___x_1057_);
                    v___x_1059_ = v_reuseFailAlloc_1062_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1060_ = lean_array_uset(v_x_1036_, v___x_1056_, v___x_1059_);
                v_x_1036_ = v___x_1060_;
                v_x_1037_ = v_tail_1040_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_i_1064_: *mut leanh::LeanObject,
    mut v_source_1065_: *mut leanh::LeanObject,
    mut v_target_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v_es_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1067_ = lean_array_get_size(v_source_1065_);
                v___x_1068_ = lean_nat_dec_lt(v_i_1064_, v___x_1067_);
                if v___x_1068_ == 0 {
                    leanh::lean_dec_ref(v_source_1065_);
                    leanh::lean_dec(v_i_1064_);
                    return v_target_1066_;
                } else {
                    v_es_1069_ = lean_array_fget(v_source_1065_, v_i_1064_);
                    v___x_1070_ = leanh::lean_box(0);
                    v_source_1071_ = lean_array_fset(v_source_1065_, v_i_1064_, v___x_1070_);
                    v_target_1072_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_1066_, v_es_1069_);
                    v___x_1073_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1074_ = lean_nat_add(v_i_1064_, v___x_1073_);
                    leanh::lean_dec(v_i_1064_);
                    v_i_1064_ = v___x_1074_;
                    v_source_1065_ = v_source_1071_;
                    v_target_1066_ = v_target_1072_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(
    mut v_data_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1077_ = lean_array_get_size(v_data_1076_);
    v___x_1078_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1079_ = lean_nat_mul(v___x_1077_, v___x_1078_);
    v___x_1080_ = leanh::lean_unsigned_to_nat(0);
    v___x_1081_ = leanh::lean_box(0);
    v___x_1082_ = lean_mk_array(v_nbuckets_1079_, v___x_1081_);
    v___x_1083_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_1080_, v_data_1076_, v___x_1082_);
    return v___x_1083_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(
    mut v_a_1084_: *mut leanh::LeanObject,
    mut v_x_1085_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1086_: u8 = 0;
    let mut v_key_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1085_) == 0 {
                    v___x_1086_ = 0;
                    return v___x_1086_;
                } else {
                    v_key_1087_ = leanh::lean_ctor_get(v_x_1085_, 0);
                    v_tail_1088_ = leanh::lean_ctor_get(v_x_1085_, 2);
                    v___x_1089_ = lean_string_dec_eq(v_key_1087_, v_a_1084_);
                    if v___x_1089_ == 0 {
                        v_x_1085_ = v_tail_1088_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1089_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_a_1091_: *mut leanh::LeanObject,
    mut v_x_1092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1093_: u8 = 0;
    let mut v_r_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1093_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_1091_, v_x_1092_);
    leanh::lean_dec(v_x_1092_);
    leanh::lean_dec_ref(v_a_1091_);
    v_r_1094_ = leanh::lean_box((v_res_1093_) as usize);
    return v_r_1094_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(
    mut v_a_1095_: *mut leanh::LeanObject,
    mut v_b_1096_: *mut leanh::LeanObject,
    mut v_x_1097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1103_: u8 = 0;
    let mut v___x_1104_: u8 = 0;
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1097_) == 0 {
                    leanh::lean_dec(v_b_1096_);
                    leanh::lean_dec_ref(v_a_1095_);
                    return v_x_1097_;
                } else {
                    v_key_1098_ = leanh::lean_ctor_get(v_x_1097_, 0);
                    v_value_1099_ = leanh::lean_ctor_get(v_x_1097_, 1);
                    v_tail_1100_ = leanh::lean_ctor_get(v_x_1097_, 2);
                    v_isSharedCheck_1112_ = (!leanh::lean_is_exclusive(v_x_1097_)) as u8;
                    if v_isSharedCheck_1112_ == 0 {
                        v___x_1102_ = v_x_1097_;
                        v_isShared_1103_ = v_isSharedCheck_1112_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1100_);
                        leanh::lean_inc(v_value_1099_);
                        leanh::lean_inc(v_key_1098_);
                        leanh::lean_dec(v_x_1097_);
                        v___x_1102_ = leanh::lean_box(0);
                        v_isShared_1103_ = v_isSharedCheck_1112_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1104_ = lean_string_dec_eq(v_key_1098_, v_a_1095_);
                if v___x_1104_ == 0 {
                    v___x_1105_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_1095_, v_b_1096_, v_tail_1100_);
                    if v_isShared_1103_ == 0 {
                        leanh::lean_ctor_set(v___x_1102_, 2, v___x_1105_);
                        v___x_1107_ = v___x_1102_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1108_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_key_1098_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_value_1099_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 2, v___x_1105_);
                        v___x_1107_ = v_reuseFailAlloc_1108_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1099_);
                    leanh::lean_dec(v_key_1098_);
                    if v_isShared_1103_ == 0 {
                        leanh::lean_ctor_set(v___x_1102_, 1, v_b_1096_);
                        leanh::lean_ctor_set(v___x_1102_, 0, v_a_1095_);
                        v___x_1110_ = v___x_1102_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1111_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1095_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_b_1096_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_tail_1100_);
                        v___x_1110_ = v_reuseFailAlloc_1111_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1107_;
            }
            3 => {
                return v___x_1110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(
    mut v_m_1113_: *mut leanh::LeanObject,
    mut v_a_1114_: *mut leanh::LeanObject,
    mut v_b_1115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1120_: u8 = 0;
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: u64 = 0;
    let mut v___x_1123_: u64 = 0;
    let mut v___x_1124_: u64 = 0;
    let mut v_fold_1125_: u64 = 0;
    let mut v___x_1126_: u64 = 0;
    let mut v___x_1127_: u64 = 0;
    let mut v___x_1128_: u64 = 0;
    let mut v___x_1129_: usize = 0;
    let mut v___x_1130_: usize = 0;
    let mut v___x_1131_: usize = 0;
    let mut v___x_1132_: usize = 0;
    let mut v___x_1133_: usize = 0;
    let mut v_bkt_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u8 = 0;
    let mut v_val_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1116_ = leanh::lean_ctor_get(v_m_1113_, 0);
                v_buckets_1117_ = leanh::lean_ctor_get(v_m_1113_, 1);
                v_isSharedCheck_1160_ = (!leanh::lean_is_exclusive(v_m_1113_)) as u8;
                if v_isSharedCheck_1160_ == 0 {
                    v___x_1119_ = v_m_1113_;
                    v_isShared_1120_ = v_isSharedCheck_1160_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1117_);
                    leanh::lean_inc(v_size_1116_);
                    leanh::lean_dec(v_m_1113_);
                    v___x_1119_ = leanh::lean_box(0);
                    v_isShared_1120_ = v_isSharedCheck_1160_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1121_ = lean_array_get_size(v_buckets_1117_);
                v___x_1122_ = lean_string_hash(v_a_1114_);
                v___x_1123_ = 32u64;
                v___x_1124_ = lean_uint64_shift_right(v___x_1122_, v___x_1123_);
                v_fold_1125_ = lean_uint64_xor(v___x_1122_, v___x_1124_);
                v___x_1126_ = 16u64;
                v___x_1127_ = lean_uint64_shift_right(v_fold_1125_, v___x_1126_);
                v___x_1128_ = lean_uint64_xor(v_fold_1125_, v___x_1127_);
                v___x_1129_ = lean_uint64_to_usize(v___x_1128_);
                v___x_1130_ = lean_usize_of_nat(v___x_1121_);
                v___x_1131_ = 1usize;
                v___x_1132_ = lean_usize_sub(v___x_1130_, v___x_1131_);
                v___x_1133_ = lean_usize_land(v___x_1129_, v___x_1132_);
                v_bkt_1134_ = lean_array_uget_borrowed(v_buckets_1117_, v___x_1133_);
                v___x_1135_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_1114_, v_bkt_1134_);
                if v___x_1135_ == 0 {
                    v___x_1136_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1137_ = lean_nat_add(v_size_1116_, v___x_1136_);
                    leanh::lean_dec(v_size_1116_);
                    leanh::lean_inc(v_bkt_1134_);
                    v___x_1138_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1138_, 0, v_a_1114_);
                    leanh::lean_ctor_set(v___x_1138_, 1, v_b_1115_);
                    leanh::lean_ctor_set(v___x_1138_, 2, v_bkt_1134_);
                    v_buckets_x27_1139_ =
                        lean_array_uset(v_buckets_1117_, v___x_1133_, v___x_1138_);
                    v___x_1140_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1141_ = lean_nat_mul(v_size_x27_1137_, v___x_1140_);
                    v___x_1142_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1143_ = lean_nat_div(v___x_1141_, v___x_1142_);
                    leanh::lean_dec(v___x_1141_);
                    v___x_1144_ = lean_array_get_size(v_buckets_x27_1139_);
                    v___x_1145_ = lean_nat_dec_le(v___x_1143_, v___x_1144_);
                    leanh::lean_dec(v___x_1143_);
                    if v___x_1145_ == 0 {
                        v_val_1146_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_1139_);
                        if v_isShared_1120_ == 0 {
                            leanh::lean_ctor_set(v___x_1119_, 1, v_val_1146_);
                            leanh::lean_ctor_set(v___x_1119_, 0, v_size_x27_1137_);
                            v___x_1148_ = v___x_1119_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1149_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1149_,
                                0,
                                v_size_x27_1137_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_val_1146_);
                            v___x_1148_ = v_reuseFailAlloc_1149_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1120_ == 0 {
                            leanh::lean_ctor_set(v___x_1119_, 1, v_buckets_x27_1139_);
                            leanh::lean_ctor_set(v___x_1119_, 0, v_size_x27_1137_);
                            v___x_1151_ = v___x_1119_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1152_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1152_,
                                0,
                                v_size_x27_1137_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1152_,
                                1,
                                v_buckets_x27_1139_,
                            );
                            v___x_1151_ = v_reuseFailAlloc_1152_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_1134_);
                    v___x_1153_ = leanh::lean_box(0);
                    v_buckets_x27_1154_ =
                        lean_array_uset(v_buckets_1117_, v___x_1133_, v___x_1153_);
                    v___x_1155_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_1114_, v_b_1115_, v_bkt_1134_);
                    v___x_1156_ = lean_array_uset(v_buckets_x27_1154_, v___x_1133_, v___x_1155_);
                    if v_isShared_1120_ == 0 {
                        leanh::lean_ctor_set(v___x_1119_, 1, v___x_1156_);
                        v___x_1158_ = v___x_1119_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1159_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_size_1116_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1156_);
                        v___x_1158_ = v_reuseFailAlloc_1159_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1148_;
            }
            3 => {
                return v___x_1151_;
            }
            4 => {
                return v___x_1158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(
    mut v_as_x27_1161_: *mut leanh::LeanObject,
    mut v_b_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_1161_) == 0 {
                    return v_b_1162_;
                } else {
                    v_head_1163_ = leanh::lean_ctor_get(v_as_x27_1161_, 0);
                    v_tail_1164_ = leanh::lean_ctor_get(v_as_x27_1161_, 1);
                    v_fst_1165_ = leanh::lean_ctor_get(v_head_1163_, 0);
                    v_snd_1166_ = leanh::lean_ctor_get(v_head_1163_, 1);
                    leanh::lean_inc(v_snd_1166_);
                    leanh::lean_inc(v_fst_1165_);
                    v_r_1167_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_b_1162_, v_fst_1165_, v_snd_1166_);
                    v_as_x27_1161_ = v_tail_1164_;
                    v_b_1162_ = v_r_1167_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg___boxed(
    mut v_as_x27_1169_: *mut leanh::LeanObject,
    mut v_b_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_1169_, v_b_1170_);
    leanh::lean_dec(v_as_x27_1169_);
    return v_res_1171_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(
    mut v_m_1172_: *mut leanh::LeanObject,
    mut v_l_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_l_1173_, v_m_1172_);
    return v___x_1174_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0___boxed(
    mut v_m_1175_: *mut leanh::LeanObject,
    mut v_l_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0(v_m_1175_, v_l_1176_);
    leanh::lean_dec(v_l_1176_);
    return v_res_1177_;
}
pub unsafe fn _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1193_ = leanh::lean_box(0);
    v___x_1194_ = leanh::lean_unsigned_to_nat(16);
    v___x_1195_ = lean_mk_array(v___x_1194_, v___x_1193_);
    return v___x_1195_;
}
pub unsafe fn _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1196_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7),
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7_once
        ),
        _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__7,
    );
    v___x_1197_ = leanh::lean_unsigned_to_nat(0);
    v___x_1198_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1198_, 0, v___x_1197_);
    leanh::lean_ctor_set(v___x_1198_, 1, v___x_1196_);
    return v___x_1198_;
}
pub unsafe fn _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1199_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8),
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8_once
        ),
        _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__8,
    );
    v___x_1200_ = l___private_Lean_DocString_Links_0__Lean_domainMap___closed__6;
    v___x_1201_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v___x_1200_, v___x_1199_);
    return v___x_1201_;
}
pub unsafe fn _init_l___private_Lean_DocString_Links_0__Lean_domainMap()
-> *mut leanh::LeanObject {
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9),
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9_once
        ),
        _init_l___private_Lean_DocString_Links_0__Lean_domainMap___closed__9,
    );
    return v___x_1202_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0(
    mut v_00_u03b2_1203_: *mut leanh::LeanObject,
    mut v_m_1204_: *mut leanh::LeanObject,
    mut v_a_1205_: *mut leanh::LeanObject,
    mut v_b_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1207_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0___redArg(v_m_1204_, v_a_1205_, v_b_1206_);
    return v___x_1207_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(
    mut v_as_1208_: *mut leanh::LeanObject,
    mut v_as_x27_1209_: *mut leanh::LeanObject,
    mut v_b_1210_: *mut leanh::LeanObject,
    mut v_a_1211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___redArg(v_as_x27_1209_, v_b_1210_);
    return v___x_1212_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1___boxed(
    mut v_as_1213_: *mut leanh::LeanObject,
    mut v_as_x27_1214_: *mut leanh::LeanObject,
    mut v_b_1215_: *mut leanh::LeanObject,
    mut v_a_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1217_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__1(v_as_1213_, v_as_x27_1214_, v_b_1215_, v_a_1216_);
    leanh::lean_dec(v_as_x27_1214_);
    leanh::lean_dec(v_as_1213_);
    return v_res_1217_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1218_: *mut leanh::LeanObject,
    mut v_a_1219_: *mut leanh::LeanObject,
    mut v_x_1220_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1221_: u8 = 0;
    v___x_1221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___redArg(v_a_1219_, v_x_1220_);
    return v___x_1221_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1222_: *mut leanh::LeanObject,
    mut v_a_1223_: *mut leanh::LeanObject,
    mut v_x_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1225_: u8 = 0;
    let mut v_r_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1225_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__1(v_00_u03b2_1222_, v_a_1223_, v_x_1224_);
    leanh::lean_dec(v_x_1224_);
    leanh::lean_dec_ref(v_a_1223_);
    v_r_1226_ = leanh::lean_box((v_res_1225_) as usize);
    return v_r_1226_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1227_: *mut leanh::LeanObject,
    mut v_data_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2___redArg(v_data_1228_);
    return v___x_1229_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3(
    mut v_00_u03b2_1230_: *mut leanh::LeanObject,
    mut v_a_1231_: *mut leanh::LeanObject,
    mut v_b_1232_: *mut leanh::LeanObject,
    mut v_x_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1234_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__3___redArg(v_a_1231_, v_b_1232_, v_x_1233_);
    return v___x_1234_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_1235_: *mut leanh::LeanObject,
    mut v_i_1236_: *mut leanh::LeanObject,
    mut v_source_1237_: *mut leanh::LeanObject,
    mut v_target_1238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1239_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_1236_, v_source_1237_, v_target_1238_);
    return v___x_1239_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b2_1240_: *mut leanh::LeanObject,
    mut v_x_1241_: *mut leanh::LeanObject,
    mut v_x_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_DocString_Links_0__Lean_domainMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_1241_, v_x_1242_);
    return v___x_1243_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(
    mut v_x_1244_: *mut leanh::LeanObject,
    mut v_x_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1245_) == 0 {
        leanh::lean_inc(v_x_1244_);
        return v_x_1244_;
    } else {
        let mut v_key_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_1246_ = leanh::lean_ctor_get(v_x_1245_, 0);
        v_tail_1247_ = leanh::lean_ctor_get(v_x_1245_, 2);
        v___x_1248_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(
            v_x_1244_,
            v_tail_1247_,
        );
        leanh::lean_inc(v_key_1246_);
        v___x_1249_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1249_, 0, v_key_1246_);
        leanh::lean_ctor_set(v___x_1249_, 1, v___x_1248_);
        return v___x_1249_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0___boxed(
    mut v_x_1250_: *mut leanh::LeanObject,
    mut v_x_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1252_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(
        v_x_1250_, v_x_1251_,
    );
    leanh::lean_dec(v_x_1251_);
    leanh::lean_dec(v_x_1250_);
    return v_res_1252_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(
    mut v_as_1253_: *mut leanh::LeanObject,
    mut v_i_1254_: usize,
    mut v_stop_1255_: usize,
    mut v_b_1256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1257_: u8 = 0;
    let mut v___x_1258_: usize = 0;
    let mut v___x_1259_: usize = 0;
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1257_ = lean_usize_dec_eq(v_i_1254_, v_stop_1255_);
                if v___x_1257_ == 0 {
                    v___x_1258_ = 1usize;
                    v___x_1259_ = lean_usize_sub(v_i_1254_, v___x_1258_);
                    v___x_1260_ = lean_array_uget_borrowed(v_as_1253_, v___x_1259_);
                    v___x_1261_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualDomains_spec__0(v_b_1256_, v___x_1260_);
                    leanh::lean_dec(v_b_1256_);
                    v_i_1254_ = v___x_1259_;
                    v_b_1256_ = v___x_1261_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1256_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1___boxed(
    mut v_as_1263_: *mut leanh::LeanObject,
    mut v_i_1264_: *mut leanh::LeanObject,
    mut v_stop_1265_: *mut leanh::LeanObject,
    mut v_b_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1267_: usize = 0;
    let mut v_stop_boxed_1268_: usize = 0;
    let mut v_res_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1267_ = leanh::lean_unbox_usize(v_i_1264_);
    leanh::lean_dec(v_i_1264_);
    v_stop_boxed_1268_ = leanh::lean_unbox_usize(v_stop_1265_);
    leanh::lean_dec(v_stop_1265_);
    v_res_1269_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_as_1263_, v_i_boxed_1267_, v_stop_boxed_1268_, v_b_1266_);
    leanh::lean_dec_ref(v_as_1263_);
    return v_res_1269_;
}
pub unsafe fn _init_l_Lean_manualDomains() -> *mut leanh::LeanObject {
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: u8 = 0;
    v___x_1270_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
    v_buckets_1271_ = leanh::lean_ctor_get(v___x_1270_, 1);
    v___x_1272_ = leanh::lean_box(0);
    v___x_1273_ = lean_array_get_size(v_buckets_1271_);
    v___x_1274_ = leanh::lean_unsigned_to_nat(0);
    v___x_1275_ = lean_nat_dec_lt(v___x_1274_, v___x_1273_);
    if v___x_1275_ == 0 {
        return v___x_1272_;
    } else {
        let mut v___x_1276_: usize = 0;
        let mut v___x_1277_: usize = 0;
        let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1276_ = lean_usize_of_nat(v___x_1273_);
        v___x_1277_ = 0usize;
        v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualDomains_spec__1(v_buckets_1271_, v___x_1276_, v___x_1277_, v___x_1272_);
        return v___x_1278_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(
    mut v_a_1279_: *mut leanh::LeanObject,
    mut v_x_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1280_) == 0 {
                    v___x_1281_ = leanh::lean_box(0);
                    return v___x_1281_;
                } else {
                    v_key_1282_ = leanh::lean_ctor_get(v_x_1280_, 0);
                    v_value_1283_ = leanh::lean_ctor_get(v_x_1280_, 1);
                    v_tail_1284_ = leanh::lean_ctor_get(v_x_1280_, 2);
                    v___x_1285_ = lean_string_dec_eq(v_key_1282_, v_a_1279_);
                    if v___x_1285_ == 0 {
                        v_x_1280_ = v_tail_1284_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1283_);
                        v___x_1287_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1287_, 0, v_value_1283_);
                        return v___x_1287_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg___boxed(
    mut v_a_1288_: *mut leanh::LeanObject,
    mut v_x_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1290_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_1288_, v_x_1289_);
    leanh::lean_dec(v_x_1289_);
    leanh::lean_dec_ref(v_a_1288_);
    return v_res_1290_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(
    mut v_m_1291_: *mut leanh::LeanObject,
    mut v_a_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u64 = 0;
    let mut v___x_1296_: u64 = 0;
    let mut v___x_1297_: u64 = 0;
    let mut v_fold_1298_: u64 = 0;
    let mut v___x_1299_: u64 = 0;
    let mut v___x_1300_: u64 = 0;
    let mut v___x_1301_: u64 = 0;
    let mut v___x_1302_: usize = 0;
    let mut v___x_1303_: usize = 0;
    let mut v___x_1304_: usize = 0;
    let mut v___x_1305_: usize = 0;
    let mut v___x_1306_: usize = 0;
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1293_ = leanh::lean_ctor_get(v_m_1291_, 1);
    v___x_1294_ = lean_array_get_size(v_buckets_1293_);
    v___x_1295_ = lean_string_hash(v_a_1292_);
    v___x_1296_ = 32u64;
    v___x_1297_ = lean_uint64_shift_right(v___x_1295_, v___x_1296_);
    v_fold_1298_ = lean_uint64_xor(v___x_1295_, v___x_1297_);
    v___x_1299_ = 16u64;
    v___x_1300_ = lean_uint64_shift_right(v_fold_1298_, v___x_1299_);
    v___x_1301_ = lean_uint64_xor(v_fold_1298_, v___x_1300_);
    v___x_1302_ = lean_uint64_to_usize(v___x_1301_);
    v___x_1303_ = lean_usize_of_nat(v___x_1294_);
    v___x_1304_ = 1usize;
    v___x_1305_ = lean_usize_sub(v___x_1303_, v___x_1304_);
    v___x_1306_ = lean_usize_land(v___x_1302_, v___x_1305_);
    v___x_1307_ = lean_array_uget_borrowed(v_buckets_1293_, v___x_1306_);
    v___x_1308_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_1292_, v___x_1307_);
    return v___x_1308_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg___boxed(
    mut v_m_1309_: *mut leanh::LeanObject,
    mut v_a_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1311_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(
            v_m_1309_, v_a_1310_,
        );
    leanh::lean_dec_ref(v_a_1310_);
    leanh::lean_dec_ref(v_m_1309_);
    return v_res_1311_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(
    mut v_x_1312_: *mut leanh::LeanObject,
    mut v_x_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1313_) == 0 {
        leanh::lean_inc(v_x_1312_);
        return v_x_1312_;
    } else {
        let mut v_key_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_1314_ = leanh::lean_ctor_get(v_x_1313_, 0);
        v_value_1315_ = leanh::lean_ctor_get(v_x_1313_, 1);
        v_tail_1316_ = leanh::lean_ctor_get(v_x_1313_, 2);
        v___x_1317_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(
            v_x_1312_,
            v_tail_1316_,
        );
        leanh::lean_inc(v_value_1315_);
        leanh::lean_inc(v_key_1314_);
        v___x_1318_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1318_, 0, v_key_1314_);
        leanh::lean_ctor_set(v___x_1318_, 1, v_value_1315_);
        v___x_1319_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1319_, 0, v___x_1318_);
        leanh::lean_ctor_set(v___x_1319_, 1, v___x_1317_);
        return v___x_1319_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2___boxed(
    mut v_x_1320_: *mut leanh::LeanObject,
    mut v_x_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(
        v_x_1320_, v_x_1321_,
    );
    leanh::lean_dec(v_x_1321_);
    leanh::lean_dec(v_x_1320_);
    return v_res_1322_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(
    mut v_as_1323_: *mut leanh::LeanObject,
    mut v_i_1324_: usize,
    mut v_stop_1325_: usize,
    mut v_b_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: usize = 0;
    let mut v___x_1329_: usize = 0;
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1327_ = lean_usize_dec_eq(v_i_1324_, v_stop_1325_);
                if v___x_1327_ == 0 {
                    v___x_1328_ = 1usize;
                    v___x_1329_ = lean_usize_sub(v_i_1324_, v___x_1328_);
                    v___x_1330_ = lean_array_uget_borrowed(v_as_1323_, v___x_1329_);
                    v___x_1331_ =
                        l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_manualLink_spec__2(
                            v_b_1326_,
                            v___x_1330_,
                        );
                    leanh::lean_dec(v_b_1326_);
                    v_i_1324_ = v___x_1329_;
                    v_b_1326_ = v___x_1331_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1326_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3___boxed(
    mut v_as_1333_: *mut leanh::LeanObject,
    mut v_i_1334_: *mut leanh::LeanObject,
    mut v_stop_1335_: *mut leanh::LeanObject,
    mut v_b_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1337_: usize = 0;
    let mut v_stop_boxed_1338_: usize = 0;
    let mut v_res_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1337_ = leanh::lean_unbox_usize(v_i_1334_);
    leanh::lean_dec(v_i_1334_);
    v_stop_boxed_1338_ = leanh::lean_unbox_usize(v_stop_1335_);
    leanh::lean_dec(v_stop_1335_);
    v_res_1339_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_as_1333_, v_i_boxed_1337_, v_stop_boxed_1338_, v_b_1336_);
    leanh::lean_dec_ref(v_as_1333_);
    return v_res_1339_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_manualLink_spec__1(
    mut v_a_1341_: *mut leanh::LeanObject,
    mut v_a_1342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v_fst_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1341_) == 0 {
                    v___x_1343_ = l_List_reverse___redArg(v_a_1342_);
                    return v___x_1343_;
                } else {
                    v_head_1344_ = leanh::lean_ctor_get(v_a_1341_, 0);
                    v_tail_1345_ = leanh::lean_ctor_get(v_a_1341_, 1);
                    v_isSharedCheck_1357_ = (!leanh::lean_is_exclusive(v_a_1341_)) as u8;
                    if v_isSharedCheck_1357_ == 0 {
                        v___x_1347_ = v_a_1341_;
                        v_isShared_1348_ = v_isSharedCheck_1357_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1345_);
                        leanh::lean_inc(v_head_1344_);
                        leanh::lean_dec(v_a_1341_);
                        v___x_1347_ = leanh::lean_box(0);
                        v_isShared_1348_ = v_isSharedCheck_1357_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1349_ = leanh::lean_ctor_get(v_head_1344_, 0);
                leanh::lean_inc(v_fst_1349_);
                leanh::lean_dec(v_head_1344_);
                v___x_1350_ = l_List_mapTR_loop___at___00Lean_manualLink_spec__1___closed__0;
                v___x_1351_ = lean_string_append(v___x_1350_, v_fst_1349_);
                leanh::lean_dec(v_fst_1349_);
                v___x_1352_ = lean_string_append(v___x_1351_, v___x_1350_);
                if v_isShared_1348_ == 0 {
                    leanh::lean_ctor_set(v___x_1347_, 1, v_a_1342_);
                    leanh::lean_ctor_set(v___x_1347_, 0, v___x_1352_);
                    v___x_1354_ = v___x_1347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1356_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_a_1342_);
                    v___x_1354_ = v_reuseFailAlloc_1356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1341_ = v_tail_1345_;
                v_a_1342_ = v___x_1354_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_manualLink(
    mut v_kind_1363_: *mut leanh::LeanObject,
    mut v_name_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut v_buckets_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acceptableKinds_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: usize = 0;
    let mut v___x_1400_: usize = 0;
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1365_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
                v___x_1366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_1365_, v_kind_1363_);
                if leanh::lean_obj_tag(v___x_1366_) == 1 {
                    v_val_1367_ = leanh::lean_ctor_get(v___x_1366_, 0);
                    v_isSharedCheck_1381_ = (!leanh::lean_is_exclusive(v___x_1366_)) as u8;
                    if v_isSharedCheck_1381_ == 0 {
                        v___x_1369_ = v___x_1366_;
                        v_isShared_1370_ = v_isSharedCheck_1381_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1367_);
                        leanh::lean_dec(v___x_1366_);
                        v___x_1369_ = leanh::lean_box(0);
                        v_isShared_1370_ = v_isSharedCheck_1381_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1366_);
                    v_buckets_1382_ = leanh::lean_ctor_get(v___x_1365_, 1);
                    v___x_1383_ = l_Lean_manualLink___closed__2;
                    v___x_1395_ = leanh::lean_box(0);
                    v___x_1396_ = lean_array_get_size(v_buckets_1382_);
                    v___x_1397_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1398_ = lean_nat_dec_lt(v___x_1397_, v___x_1396_);
                    if v___x_1398_ == 0 {
                        v___y_1385_ = v___x_1395_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1399_ = lean_usize_of_nat(v___x_1396_);
                        v___x_1400_ = 0usize;
                        v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_1382_, v___x_1399_, v___x_1400_, v___x_1395_);
                        v___y_1385_ = v___x_1401_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1371_ = l_Lean_manualRoot;
                v___x_1372_ = l_Lean_manualLink___closed__0;
                v___x_1373_ = lean_string_append(v___x_1372_, v_val_1367_);
                leanh::lean_dec(v_val_1367_);
                v___x_1374_ = l_Lean_manualLink___closed__1;
                v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
                v___x_1376_ = lean_string_append(v___x_1375_, v_name_1364_);
                v___x_1377_ = lean_string_append(v___x_1371_, v___x_1376_);
                leanh::lean_dec_ref(v___x_1376_);
                if v_isShared_1370_ == 0 {
                    leanh::lean_ctor_set(v___x_1369_, 0, v___x_1377_);
                    v___x_1379_ = v___x_1369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
                    v___x_1379_ = v_reuseFailAlloc_1380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1379_;
            }
            3 => {
                v___x_1386_ = leanh::lean_box(0);
                v___x_1387_ =
                    l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_1385_, v___x_1386_);
                v_acceptableKinds_1388_ = l_String_intercalate(v___x_1383_, v___x_1387_);
                v___x_1389_ = l_Lean_manualLink___closed__3;
                v___x_1390_ = lean_string_append(v___x_1389_, v_kind_1363_);
                v___x_1391_ = l_Lean_manualLink___closed__4;
                v___x_1392_ = lean_string_append(v___x_1390_, v___x_1391_);
                v___x_1393_ = lean_string_append(v___x_1392_, v_acceptableKinds_1388_);
                leanh::lean_dec_ref(v_acceptableKinds_1388_);
                v___x_1394_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1394_, 0, v___x_1393_);
                return v___x_1394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_manualLink___boxed(
    mut v_kind_1402_: *mut leanh::LeanObject,
    mut v_name_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1404_ = l_Lean_manualLink(v_kind_1402_, v_name_1403_);
    leanh::lean_dec_ref(v_name_1403_);
    leanh::lean_dec_ref(v_kind_1402_);
    return v_res_1404_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(
    mut v_00_u03b2_1405_: *mut leanh::LeanObject,
    mut v_m_1406_: *mut leanh::LeanObject,
    mut v_a_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(
            v_m_1406_, v_a_1407_,
        );
    return v___x_1408_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___boxed(
    mut v_00_u03b2_1409_: *mut leanh::LeanObject,
    mut v_m_1410_: *mut leanh::LeanObject,
    mut v_a_1411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0(
        v_00_u03b2_1409_,
        v_m_1410_,
        v_a_1411_,
    );
    leanh::lean_dec_ref(v_a_1411_);
    leanh::lean_dec_ref(v_m_1410_);
    return v_res_1412_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(
    mut v_00_u03b2_1413_: *mut leanh::LeanObject,
    mut v_a_1414_: *mut leanh::LeanObject,
    mut v_x_1415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1416_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___redArg(v_a_1414_, v_x_1415_);
    return v___x_1416_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0___boxed(
    mut v_00_u03b2_1417_: *mut leanh::LeanObject,
    mut v_a_1418_: *mut leanh::LeanObject,
    mut v_x_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1420_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0_spec__0(v_00_u03b2_1417_, v_a_1418_, v_x_1419_);
    leanh::lean_dec(v_x_1419_);
    leanh::lean_dec_ref(v_a_1418_);
    return v_res_1420_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(
    mut v_s_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___closed__0;
    return v___x_1424_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1___boxed(
    mut v_s_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ =
        l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(
            v_s_1425_,
        );
    leanh::lean_dec_ref(v_s_1425_);
    return v_res_1426_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(
    mut v_path_1427_: *mut leanh::LeanObject,
    mut v___x_1428_: *mut leanh::LeanObject,
    mut v___x_1429_: *mut leanh::LeanObject,
    mut v_a_1430_: *mut leanh::LeanObject,
    mut v_b_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v_startInclusive_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: u32 = 0;
    let mut v___x_1450_: u32 = 0;
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1430_) == 0 {
                    v_currPos_1440_ = leanh::lean_ctor_get(v_a_1430_, 0);
                    v_searcher_1441_ = leanh::lean_ctor_get(v_a_1430_, 1);
                    v_isSharedCheck_1467_ = (!leanh::lean_is_exclusive(v_a_1430_)) as u8;
                    if v_isSharedCheck_1467_ == 0 {
                        v___x_1443_ = v_a_1430_;
                        v_isShared_1444_ = v_isSharedCheck_1467_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_1441_);
                        leanh::lean_inc(v_currPos_1440_);
                        leanh::lean_dec(v_a_1430_);
                        v___x_1443_ = leanh::lean_box(0);
                        v_isShared_1444_ = v_isSharedCheck_1467_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1429_);
                    leanh::lean_dec_ref(v_path_1427_);
                    return v_b_1431_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_path_1427_);
                v___x_1436_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1436_, 0, v_path_1427_);
                leanh::lean_ctor_set(v___x_1436_, 1, v_startInclusive_1434_);
                leanh::lean_ctor_set(v___x_1436_, 2, v_endExclusive_1435_);
                v___x_1437_ = l_String_Slice_toString(v___x_1436_);
                leanh::lean_dec_ref_known(v___x_1436_, 3);
                v___x_1438_ = lean_array_push(v_b_1431_, v___x_1437_);
                v_a_1430_ = v_it_1433_;
                v_b_1431_ = v___x_1438_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1445_ = leanh::lean_ctor_get(v___x_1428_, 1);
                v_endExclusive_1446_ = leanh::lean_ctor_get(v___x_1428_, 2);
                v___x_1447_ = lean_nat_sub(v_endExclusive_1446_, v_startInclusive_1445_);
                v___x_1448_ = lean_nat_dec_eq(v_searcher_1441_, v___x_1447_);
                leanh::lean_dec(v___x_1447_);
                if v___x_1448_ == 0 {
                    v___x_1449_ = 47;
                    v___x_1450_ = lean_string_utf8_get_fast(v_path_1427_, v_searcher_1441_);
                    v___x_1451_ = lean_uint32_dec_eq(v___x_1450_, v___x_1449_);
                    if v___x_1451_ == 0 {
                        v___x_1452_ = lean_string_utf8_next_fast(v_path_1427_, v_searcher_1441_);
                        leanh::lean_dec(v_searcher_1441_);
                        if v_isShared_1444_ == 0 {
                            leanh::lean_ctor_set(v___x_1443_, 1, v___x_1452_);
                            v___x_1454_ = v___x_1443_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1456_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_currPos_1440_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1452_);
                            v___x_1454_ = v_reuseFailAlloc_1456_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1457_ = lean_string_utf8_next_fast(v_path_1427_, v_searcher_1441_);
                        v___x_1458_ = lean_nat_sub(v___x_1457_, v_searcher_1441_);
                        v___x_1459_ = lean_nat_add(v_searcher_1441_, v___x_1458_);
                        leanh::lean_dec(v___x_1458_);
                        v_slice_1460_ = l_String_Slice_subslice_x21(
                            v___x_1428_,
                            v_currPos_1440_,
                            v_searcher_1441_,
                        );
                        leanh::lean_inc(v___x_1459_);
                        if v_isShared_1444_ == 0 {
                            leanh::lean_ctor_set(v___x_1443_, 1, v___x_1459_);
                            leanh::lean_ctor_set(v___x_1443_, 0, v___x_1459_);
                            v_nextIt_1462_ = v___x_1443_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1465_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1459_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1459_);
                            v_nextIt_1462_ = v_reuseFailAlloc_1465_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1443_);
                    leanh::lean_dec(v_searcher_1441_);
                    v___x_1466_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_1429_);
                    v_it_1433_ = v___x_1466_;
                    v_startInclusive_1434_ = v_currPos_1440_;
                    v_endExclusive_1435_ = v___x_1429_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_1430_ = v___x_1454_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1463_ = leanh::lean_ctor_get(v_slice_1460_, 0);
                leanh::lean_inc(v_startInclusive_1463_);
                v_endExclusive_1464_ = leanh::lean_ctor_get(v_slice_1460_, 1);
                leanh::lean_inc(v_endExclusive_1464_);
                leanh::lean_dec_ref(v_slice_1460_);
                v_it_1433_ = v_nextIt_1462_;
                v_startInclusive_1434_ = v_startInclusive_1463_;
                v_endExclusive_1435_ = v_endExclusive_1464_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg___boxed(
    mut v_path_1468_: *mut leanh::LeanObject,
    mut v___x_1469_: *mut leanh::LeanObject,
    mut v___x_1470_: *mut leanh::LeanObject,
    mut v_a_1471_: *mut leanh::LeanObject,
    mut v_b_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1473_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_1468_, v___x_1469_, v___x_1470_, v_a_1471_, v_b_1472_);
    leanh::lean_dec_ref(v___x_1469_);
    return v_res_1473_;
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(
    mut v_x_1474_: *mut leanh::LeanObject,
    mut v_x_1475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1475_) == 0 {
                    return v_x_1474_;
                } else {
                    v_head_1476_ = leanh::lean_ctor_get(v_x_1475_, 0);
                    v_tail_1477_ = leanh::lean_ctor_get(v_x_1475_, 1);
                    v___x_1478_ = l_Lean_manualLink___closed__2;
                    v___x_1479_ = lean_string_append(v_x_1474_, v___x_1478_);
                    v___x_1480_ = lean_string_append(v___x_1479_, v_head_1476_);
                    v_x_1474_ = v___x_1480_;
                    v_x_1475_ = v_tail_1477_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0___boxed(
    mut v_x_1482_: *mut leanh::LeanObject,
    mut v_x_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1484_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v_x_1482_, v_x_1483_);
    leanh::lean_dec(v_x_1483_);
    return v_res_1484_;
}
pub unsafe fn l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(
    mut v_x_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1488_) == 0 {
        let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1489_ =
            l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__0;
        return v___x_1489_;
    } else {
        let mut v_tail_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1490_ = leanh::lean_ctor_get(v_x_1488_, 1);
        if leanh::lean_obj_tag(v_tail_1490_) == 0 {
            let mut v_head_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_1491_ = leanh::lean_ctor_get(v_x_1488_, 0);
            v___x_1492_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1;
            v___x_1493_ = lean_string_append(v___x_1492_, v_head_1491_);
            v___x_1494_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__2;
            v___x_1495_ = lean_string_append(v___x_1493_, v___x_1494_);
            return v___x_1495_;
        } else {
            let mut v_head_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1500_: u32 = 0;
            let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_1496_ = leanh::lean_ctor_get(v_x_1488_, 0);
            v___x_1497_ = l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___closed__1;
            v___x_1498_ = lean_string_append(v___x_1497_, v_head_1496_);
            v___x_1499_ = l_List_foldl___at___00List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0_spec__0(v___x_1498_, v_tail_1490_);
            v___x_1500_ = 93;
            v___x_1501_ = lean_string_push(v___x_1499_, v___x_1500_);
            return v___x_1501_;
        }
    }
}
pub unsafe fn l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0___boxed(
    mut v_x_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1503_ =
        l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(v_x_1502_);
    leanh::lean_dec(v_x_1502_);
    return v_res_1503_;
}
pub unsafe fn l___private_Lean_DocString_Links_0__Lean_rw(
    mut v_path_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acceptableKinds_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1557_: u8 = 0;
    let mut v_head_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: u8 = 0;
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_buckets_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1540_ = leanh::lean_unsigned_to_nat(0);
                v___x_1541_ = lean_string_utf8_byte_size(v_path_1514_);
                leanh::lean_inc_ref(v_path_1514_);
                v___x_1542_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1542_, 0, v_path_1514_);
                leanh::lean_ctor_set(v___x_1542_, 1, v___x_1540_);
                leanh::lean_ctor_set(v___x_1542_, 2, v___x_1541_);
                v___x_1543_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__1(v___x_1542_);
                v___x_1544_ = l___private_Lean_DocString_Links_0__Lean_rw___closed__4;
                v___x_1545_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_1514_, v___x_1542_, v___x_1541_, v___x_1543_, v___x_1544_);
                leanh::lean_dec_ref_known(v___x_1542_, 3);
                v___x_1546_ = lean_array_to_list(v___x_1545_);
                if leanh::lean_obj_tag(v___x_1546_) == 0 {
                    state = 3;
                    continue;
                } else {
                    v_head_1547_ = leanh::lean_ctor_get(v___x_1546_, 0);
                    leanh::lean_inc(v_head_1547_);
                    v_tail_1548_ = leanh::lean_ctor_get(v___x_1546_, 1);
                    leanh::lean_inc(v_tail_1548_);
                    leanh::lean_dec_ref_known(v___x_1546_, 2);
                    v___x_1585_ = l___private_Lean_DocString_Links_0__Lean_rw___closed__7;
                    v___x_1586_ = lean_string_dec_eq(v_head_1547_, v___x_1585_);
                    if v___x_1586_ == 0 {
                        v_kind_1550_ = v_head_1547_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_head_1547_);
                        if leanh::lean_obj_tag(v_tail_1548_) == 0 {
                            state = 3;
                            continue;
                        } else {
                            v_kind_1550_ = v___x_1585_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1519_ = leanh::lean_box(0);
                v___x_1520_ =
                    l_List_mapTR_loop___at___00Lean_manualLink_spec__1(v___y_1518_, v___x_1519_);
                v_acceptableKinds_1521_ = l_String_intercalate(v___y_1517_, v___x_1520_);
                v___x_1522_ = l_Lean_manualLink___closed__3;
                v___x_1523_ = lean_string_append(v___x_1522_, v___y_1516_);
                leanh::lean_dec_ref(v___y_1516_);
                v___x_1524_ = l_Lean_manualLink___closed__4;
                v___x_1525_ = lean_string_append(v___x_1523_, v___x_1524_);
                v___x_1526_ = lean_string_append(v___x_1525_, v_acceptableKinds_1521_);
                leanh::lean_dec_ref(v_acceptableKinds_1521_);
                v___x_1527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
                return v___x_1527_;
            }
            2 => {
                v___x_1531_ = l___private_Lean_DocString_Links_0__Lean_rw___closed__0;
                v___x_1532_ = lean_string_append(v___x_1531_, v___y_1529_);
                leanh::lean_dec_ref(v___y_1529_);
                v___x_1533_ = l___private_Lean_DocString_Links_0__Lean_rw___closed__1;
                v___x_1534_ = lean_string_append(v___x_1532_, v___x_1533_);
                v___x_1535_ =
                    l_List_toString___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__0(
                        v___y_1530_,
                    );
                leanh::lean_dec(v___y_1530_);
                v___x_1536_ = lean_string_append(v___x_1534_, v___x_1535_);
                leanh::lean_dec_ref(v___x_1535_);
                v___x_1537_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1537_, 0, v___x_1536_);
                return v___x_1537_;
            }
            3 => {
                v___x_1539_ = l___private_Lean_DocString_Links_0__Lean_rw___closed__3;
                return v___x_1539_;
            }
            4 => {
                v___x_1551_ = l___private_Lean_DocString_Links_0__Lean_domainMap;
                v___x_1552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_manualLink_spec__0___redArg(v___x_1551_, v_kind_1550_);
                if leanh::lean_obj_tag(v___x_1552_) == 1 {
                    if leanh::lean_obj_tag(v_tail_1548_) == 1 {
                        v_tail_1553_ = leanh::lean_ctor_get(v_tail_1548_, 1);
                        if leanh::lean_obj_tag(v_tail_1553_) == 0 {
                            v_val_1554_ = leanh::lean_ctor_get(v___x_1552_, 0);
                            v_isSharedCheck_1576_ =
                                (!leanh::lean_is_exclusive(v___x_1552_)) as u8;
                            if v_isSharedCheck_1576_ == 0 {
                                v___x_1556_ = v___x_1552_;
                                v_isShared_1557_ = v_isSharedCheck_1576_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_1554_);
                                leanh::lean_dec(v___x_1552_);
                                v___x_1556_ = leanh::lean_box(0);
                                v_isShared_1557_ = v_isSharedCheck_1576_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_1552_, 1);
                            v___y_1529_ = v_kind_1550_;
                            v___y_1530_ = v_tail_1548_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_1552_, 1);
                        v___y_1529_ = v_kind_1550_;
                        v___y_1530_ = v_tail_1548_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1552_);
                    leanh::lean_dec(v_tail_1548_);
                    v_buckets_1577_ = leanh::lean_ctor_get(v___x_1551_, 1);
                    v___x_1578_ = l_Lean_manualLink___closed__2;
                    v___x_1579_ = leanh::lean_box(0);
                    v___x_1580_ = lean_array_get_size(v_buckets_1577_);
                    v___x_1581_ = lean_nat_dec_lt(v___x_1540_, v___x_1580_);
                    if v___x_1581_ == 0 {
                        v___y_1516_ = v_kind_1550_;
                        v___y_1517_ = v___x_1578_;
                        v___y_1518_ = v___x_1579_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1582_ = lean_usize_of_nat(v___x_1580_);
                        v___x_1583_ = 0usize;
                        v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_manualLink_spec__3(v_buckets_1577_, v___x_1582_, v___x_1583_, v___x_1579_);
                        v___y_1516_ = v_kind_1550_;
                        v___y_1517_ = v___x_1578_;
                        v___y_1518_ = v___x_1584_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                v_head_1558_ = leanh::lean_ctor_get(v_tail_1548_, 0);
                leanh::lean_inc(v_head_1558_);
                leanh::lean_dec_ref_known(v_tail_1548_, 2);
                v___x_1559_ = lean_string_utf8_byte_size(v_head_1558_);
                v___x_1560_ = lean_nat_dec_eq(v___x_1559_, v___x_1540_);
                if v___x_1560_ == 0 {
                    leanh::lean_dec_ref(v_kind_1550_);
                    v___x_1561_ = l_Lean_manualLink___closed__0;
                    v___x_1562_ = lean_string_append(v___x_1561_, v_val_1554_);
                    leanh::lean_dec(v_val_1554_);
                    v___x_1563_ = l_Lean_manualLink___closed__1;
                    v___x_1564_ = lean_string_append(v___x_1562_, v___x_1563_);
                    v___x_1565_ = lean_string_append(v___x_1564_, v_head_1558_);
                    leanh::lean_dec(v_head_1558_);
                    if v_isShared_1557_ == 0 {
                        leanh::lean_ctor_set(v___x_1556_, 0, v___x_1565_);
                        v___x_1567_ = v___x_1556_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1568_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
                        v___x_1567_ = v_reuseFailAlloc_1568_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_head_1558_);
                    leanh::lean_dec(v_val_1554_);
                    v___x_1569_ = l___private_Lean_DocString_Links_0__Lean_rw___closed__5;
                    v___x_1570_ = lean_string_append(v___x_1569_, v_kind_1550_);
                    leanh::lean_dec_ref(v_kind_1550_);
                    v___x_1571_ = l___private_Lean_DocString_Links_0__Lean_rw___closed__6;
                    v___x_1572_ = lean_string_append(v___x_1570_, v___x_1571_);
                    if v_isShared_1557_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1556_, 0);
                        leanh::lean_ctor_set(v___x_1556_, 0, v___x_1572_);
                        v___x_1574_ = v___x_1556_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1575_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
                        v___x_1574_ = v_reuseFailAlloc_1575_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1567_;
            }
            7 => {
                return v___x_1574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(
    mut v_path_1587_: *mut leanh::LeanObject,
    mut v___x_1588_: *mut leanh::LeanObject,
    mut v___x_1589_: *mut leanh::LeanObject,
    mut v_inst_1590_: *mut leanh::LeanObject,
    mut v_R_1591_: *mut leanh::LeanObject,
    mut v_a_1592_: *mut leanh::LeanObject,
    mut v_b_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___redArg(v_path_1587_, v___x_1588_, v___x_1589_, v_a_1592_, v_b_1593_);
    return v___x_1594_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2___boxed(
    mut v_path_1595_: *mut leanh::LeanObject,
    mut v___x_1596_: *mut leanh::LeanObject,
    mut v___x_1597_: *mut leanh::LeanObject,
    mut v_inst_1598_: *mut leanh::LeanObject,
    mut v_R_1599_: *mut leanh::LeanObject,
    mut v_a_1600_: *mut leanh::LeanObject,
    mut v_b_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Links_0__Lean_rw_spec__2(v_path_1595_, v___x_1596_, v___x_1597_, v_inst_1598_, v_R_1599_, v_a_1600_, v_b_1601_);
    leanh::lean_dec_ref(v___x_1596_);
    return v_res_1602_;
}
pub unsafe fn l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(
    mut v_c_1603_: u32,
) -> u8 {
    let mut v___y_1605_: u8 = 0;
    let mut v___x_1606_: u32 = 0;
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: u32 = 0;
    let mut v___x_1609_: u8 = 0;
    let mut v___x_1610_: u32 = 0;
    let mut v___x_1611_: u8 = 0;
    let mut v___x_1612_: u32 = 0;
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: u32 = 0;
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: u32 = 0;
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: u32 = 0;
    let mut v___x_1619_: u8 = 0;
    let mut v___x_1620_: u32 = 0;
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: u32 = 0;
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1624_: u32 = 0;
    let mut v___x_1625_: u8 = 0;
    let mut v___x_1626_: u32 = 0;
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1628_: u32 = 0;
    let mut v___x_1629_: u8 = 0;
    let mut v___x_1630_: u32 = 0;
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: u32 = 0;
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1634_: u32 = 0;
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: u32 = 0;
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: u32 = 0;
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: u32 = 0;
    let mut v___x_1641_: u8 = 0;
    let mut v___x_1642_: u32 = 0;
    let mut v___x_1643_: u8 = 0;
    let mut v___x_1644_: u32 = 0;
    let mut v___x_1645_: u8 = 0;
    let mut v___y_1647_: u8 = 0;
    let mut v___x_1648_: u32 = 0;
    let mut v___x_1649_: u8 = 0;
    let mut v___x_1650_: u32 = 0;
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1653_: u32 = 0;
    let mut v___x_1654_: u8 = 0;
    let mut v___x_1655_: u32 = 0;
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: u32 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: u32 = 0;
    let mut v___x_1660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1657_ = 65;
                v___x_1658_ = lean_uint32_dec_le(v___x_1657_, v_c_1603_);
                if v___x_1658_ == 0 {
                    state = 3;
                    continue;
                } else {
                    v___x_1659_ = 90;
                    v___x_1660_ = lean_uint32_dec_le(v_c_1603_, v___x_1659_);
                    if v___x_1660_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        return v___x_1660_;
                    }
                }
            }
            1 => {
                if v___y_1605_ == 0 {
                    v___x_1606_ = 45;
                    v___x_1607_ = lean_uint32_dec_eq(v_c_1603_, v___x_1606_);
                    if v___x_1607_ == 0 {
                        v___x_1608_ = 46;
                        v___x_1609_ = lean_uint32_dec_eq(v_c_1603_, v___x_1608_);
                        if v___x_1609_ == 0 {
                            v___x_1610_ = 95;
                            v___x_1611_ = lean_uint32_dec_eq(v_c_1603_, v___x_1610_);
                            if v___x_1611_ == 0 {
                                v___x_1612_ = 126;
                                v___x_1613_ = lean_uint32_dec_eq(v_c_1603_, v___x_1612_);
                                if v___x_1613_ == 0 {
                                    v___x_1614_ = 58;
                                    v___x_1615_ = lean_uint32_dec_eq(v_c_1603_, v___x_1614_);
                                    if v___x_1615_ == 0 {
                                        v___x_1616_ = 47;
                                        v___x_1617_ = lean_uint32_dec_eq(v_c_1603_, v___x_1616_);
                                        if v___x_1617_ == 0 {
                                            v___x_1618_ = 63;
                                            v___x_1619_ =
                                                lean_uint32_dec_eq(v_c_1603_, v___x_1618_);
                                            if v___x_1619_ == 0 {
                                                v___x_1620_ = 35;
                                                v___x_1621_ =
                                                    lean_uint32_dec_eq(v_c_1603_, v___x_1620_);
                                                if v___x_1621_ == 0 {
                                                    v___x_1622_ = 91;
                                                    v___x_1623_ =
                                                        lean_uint32_dec_eq(v_c_1603_, v___x_1622_);
                                                    if v___x_1623_ == 0 {
                                                        v___x_1624_ = 93;
                                                        v___x_1625_ = lean_uint32_dec_eq(
                                                            v_c_1603_,
                                                            v___x_1624_,
                                                        );
                                                        if v___x_1625_ == 0 {
                                                            v___x_1626_ = 64;
                                                            v___x_1627_ = lean_uint32_dec_eq(
                                                                v_c_1603_,
                                                                v___x_1626_,
                                                            );
                                                            if v___x_1627_ == 0 {
                                                                v___x_1628_ = 33;
                                                                v___x_1629_ = lean_uint32_dec_eq(
                                                                    v_c_1603_,
                                                                    v___x_1628_,
                                                                );
                                                                if v___x_1629_ == 0 {
                                                                    v___x_1630_ = 36;
                                                                    v___x_1631_ =
                                                                        lean_uint32_dec_eq(
                                                                            v_c_1603_,
                                                                            v___x_1630_,
                                                                        );
                                                                    if v___x_1631_ == 0 {
                                                                        v___x_1632_ = 38;
                                                                        v___x_1633_ =
                                                                            lean_uint32_dec_eq(
                                                                                v_c_1603_,
                                                                                v___x_1632_,
                                                                            );
                                                                        if v___x_1633_ == 0 {
                                                                            v___x_1634_ = 39;
                                                                            v___x_1635_ =
                                                                                lean_uint32_dec_eq(
                                                                                    v_c_1603_,
                                                                                    v___x_1634_,
                                                                                );
                                                                            if v___x_1635_ == 0 {
                                                                                v___x_1636_ = 42;
                                                                                v___x_1637_ = lean_uint32_dec_eq(v_c_1603_, v___x_1636_);
                                                                                if v___x_1637_ == 0
                                                                                {
                                                                                    v___x_1638_ =
                                                                                        43;
                                                                                    v___x_1639_ = lean_uint32_dec_eq(v_c_1603_, v___x_1638_);
                                                                                    if v___x_1639_
                                                                                        == 0
                                                                                    {
                                                                                        v___x_1640_ = 44;
                                                                                        v___x_1641_ = lean_uint32_dec_eq(v_c_1603_, v___x_1640_);
                                                                                        if v___x_1641_ == 0 {
v___x_1642_ = 59;
v___x_1643_ = lean_uint32_dec_eq(v_c_1603_, v___x_1642_);
if v___x_1643_ == 0 {
v___x_1644_ = 61;
v___x_1645_ = lean_uint32_dec_eq(v_c_1603_, v___x_1644_);
return v___x_1645_;
} else {
return v___x_1643_;
}
} else {
return v___x_1641_;
}
                                                                                    } else {
                                                                                        return v___x_1639_;
                                                                                    }
                                                                                } else {
                                                                                    return v___x_1637_;
                                                                                }
                                                                            } else {
                                                                                return v___x_1635_;
                                                                            }
                                                                        } else {
                                                                            return v___x_1633_;
                                                                        }
                                                                    } else {
                                                                        return v___x_1631_;
                                                                    }
                                                                } else {
                                                                    return v___x_1629_;
                                                                }
                                                            } else {
                                                                return v___x_1627_;
                                                            }
                                                        } else {
                                                            return v___x_1625_;
                                                        }
                                                    } else {
                                                        return v___x_1623_;
                                                    }
                                                } else {
                                                    return v___x_1621_;
                                                }
                                            } else {
                                                return v___x_1619_;
                                            }
                                        } else {
                                            return v___x_1617_;
                                        }
                                    } else {
                                        return v___x_1615_;
                                    }
                                } else {
                                    return v___x_1613_;
                                }
                            } else {
                                return v___x_1611_;
                            }
                        } else {
                            return v___x_1609_;
                        }
                    } else {
                        return v___x_1607_;
                    }
                } else {
                    return v___y_1605_;
                }
            }
            2 => {
                if v___y_1647_ == 0 {
                    v___x_1648_ = 48;
                    v___x_1649_ = lean_uint32_dec_le(v___x_1648_, v_c_1603_);
                    if v___x_1649_ == 0 {
                        v___y_1605_ = v___x_1649_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1650_ = 57;
                        v___x_1651_ = lean_uint32_dec_le(v_c_1603_, v___x_1650_);
                        v___y_1605_ = v___x_1651_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1647_;
                }
            }
            3 => {
                v___x_1653_ = 97;
                v___x_1654_ = lean_uint32_dec_le(v___x_1653_, v_c_1603_);
                if v___x_1654_ == 0 {
                    v___y_1647_ = v___x_1654_;
                    state = 2;
                    continue;
                } else {
                    v___x_1655_ = 122;
                    v___x_1656_ = lean_uint32_dec_le(v_c_1603_, v___x_1655_);
                    v___y_1647_ = v___x_1656_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar___boxed(
    mut v_c_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1662_: u32 = 0;
    let mut v_res_1663_: u8 = 0;
    let mut v_r_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1662_ = leanh::lean_unbox_uint32(v_c_1661_);
    leanh::lean_dec(v_c_1661_);
    v_res_1663_ =
        l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(v_c_boxed_1662_);
    v_r_1664_ = leanh::lean_box((v_res_1663_) as usize);
    return v_r_1664_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(
    mut v_s_1665_: *mut leanh::LeanObject,
    mut v___x_1666_: *mut leanh::LeanObject,
    mut v___x_1667_: *mut leanh::LeanObject,
    mut v___x_1668_: u32,
    mut v_a_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1675_: u8 = 0;
    let mut v_fst_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v_fst_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: u32 = 0;
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: u8 = 0;
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_unused_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1740_: u8 = 0;
    let mut v_unused_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1670_ = leanh::lean_ctor_get(v_a_1669_, 1);
                leanh::lean_inc(v_snd_1670_);
                v_snd_1671_ = leanh::lean_ctor_get(v_snd_1670_, 1);
                leanh::lean_inc(v_snd_1671_);
                v_fst_1672_ = leanh::lean_ctor_get(v_a_1669_, 0);
                v_isSharedCheck_1740_ = (!leanh::lean_is_exclusive(v_a_1669_)) as u8;
                if v_isSharedCheck_1740_ == 0 {
                    v_unused_1741_ = leanh::lean_ctor_get(v_a_1669_, 1);
                    leanh::lean_dec(v_unused_1741_);
                    v___x_1674_ = v_a_1669_;
                    v_isShared_1675_ = v_isSharedCheck_1740_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_1672_);
                    leanh::lean_dec(v_a_1669_);
                    v___x_1674_ = leanh::lean_box(0);
                    v_isShared_1675_ = v_isSharedCheck_1740_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1676_ = leanh::lean_ctor_get(v_snd_1670_, 0);
                v_isSharedCheck_1738_ = (!leanh::lean_is_exclusive(v_snd_1670_)) as u8;
                if v_isSharedCheck_1738_ == 0 {
                    v_unused_1739_ = leanh::lean_ctor_get(v_snd_1670_, 1);
                    leanh::lean_dec(v_unused_1739_);
                    v___x_1678_ = v_snd_1670_;
                    v_isShared_1679_ = v_isSharedCheck_1738_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_1676_);
                    leanh::lean_dec(v_snd_1670_);
                    v___x_1678_ = leanh::lean_box(0);
                    v_isShared_1679_ = v_isSharedCheck_1738_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_1680_ = leanh::lean_ctor_get(v_snd_1671_, 0);
                v_snd_1681_ = leanh::lean_ctor_get(v_snd_1671_, 1);
                v_isSharedCheck_1737_ = (!leanh::lean_is_exclusive(v_snd_1671_)) as u8;
                if v_isSharedCheck_1737_ == 0 {
                    v___x_1683_ = v_snd_1671_;
                    v_isShared_1684_ = v_isSharedCheck_1737_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1681_);
                    leanh::lean_inc(v_fst_1680_);
                    leanh::lean_dec(v_snd_1671_);
                    v___x_1683_ = leanh::lean_box(0);
                    v_isShared_1684_ = v_isSharedCheck_1737_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1685_ = lean_string_utf8_byte_size(v_s_1665_);
                v___x_1686_ = lean_nat_dec_eq(v_snd_1681_, v___x_1685_);
                if v___x_1686_ == 0 {
                    v___x_1687_ = lean_string_utf8_get_fast(v_s_1665_, v_snd_1681_);
                    v___x_1688_ = lean_string_utf8_next_fast(v_s_1665_, v_snd_1681_);
                    v___x_1726_ =
                        l___private_Lean_DocString_Links_0__Lean_rewriteManualLinksCore_urlChar(
                            v___x_1687_,
                        );
                    if v___x_1726_ == 0 {
                        v___y_1721_ = v___x_1726_;
                        state = 11;
                        continue;
                    } else {
                        v___x_1727_ = lean_nat_dec_eq(v___x_1688_, v___x_1685_);
                        if v___x_1727_ == 0 {
                            v___y_1721_ = v___x_1726_;
                            state = 11;
                            continue;
                        } else {
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1667_);
                    if v_isShared_1684_ == 0 {
                        v___x_1729_ = v___x_1683_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1736_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_fst_1680_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_snd_1681_);
                        v___x_1729_ = v_reuseFailAlloc_1736_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1690_ = lean_string_utf8_extract(v_s_1665_, v___x_1666_, v_snd_1681_);
                v___x_1691_ = l___private_Lean_DocString_Links_0__Lean_rw(v___x_1690_);
                if leanh::lean_obj_tag(v___x_1691_) == 0 {
                    v_a_1692_ = leanh::lean_ctor_get(v___x_1691_, 0);
                    leanh::lean_inc(v_a_1692_);
                    leanh::lean_dec_ref_known(v___x_1691_, 1);
                    v___x_1693_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1693_, 0, v___x_1667_);
                    leanh::lean_ctor_set(v___x_1693_, 1, v_snd_1681_);
                    if v_isShared_1684_ == 0 {
                        leanh::lean_ctor_set(v___x_1683_, 1, v_a_1692_);
                        leanh::lean_ctor_set(v___x_1683_, 0, v___x_1693_);
                        v___x_1695_ = v___x_1683_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1705_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1693_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_a_1692_);
                        v___x_1695_ = v_reuseFailAlloc_1705_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_1681_);
                    leanh::lean_dec(v_fst_1680_);
                    leanh::lean_dec(v___x_1667_);
                    v_a_1706_ = leanh::lean_ctor_get(v___x_1691_, 0);
                    leanh::lean_inc(v_a_1706_);
                    leanh::lean_dec_ref_known(v___x_1691_, 1);
                    v___x_1707_ = l_Lean_manualRoot;
                    v___x_1708_ = lean_string_append(v_fst_1672_, v___x_1707_);
                    v___x_1709_ = lean_string_append(v___x_1708_, v_a_1706_);
                    leanh::lean_dec(v_a_1706_);
                    v___x_1710_ = lean_string_push(v___x_1709_, v___x_1687_);
                    if v_isShared_1684_ == 0 {
                        leanh::lean_ctor_set(v___x_1683_, 1, v___x_1688_);
                        leanh::lean_ctor_set(v___x_1683_, 0, v___x_1688_);
                        v___x_1712_ = v___x_1683_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1719_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1688_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1688_);
                        v___x_1712_ = v_reuseFailAlloc_1719_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1696_ = lean_array_push(v_fst_1676_, v___x_1695_);
                v___x_1697_ = lean_string_push(v_fst_1672_, v___x_1668_);
                if v_isShared_1679_ == 0 {
                    leanh::lean_ctor_set(v___x_1678_, 1, v___x_1688_);
                    leanh::lean_ctor_set(v___x_1678_, 0, v_fst_1680_);
                    v___x_1699_ = v___x_1678_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1704_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_fst_1680_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1688_);
                    v___x_1699_ = v_reuseFailAlloc_1704_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1675_ == 0 {
                    leanh::lean_ctor_set(v___x_1674_, 1, v___x_1699_);
                    leanh::lean_ctor_set(v___x_1674_, 0, v___x_1696_);
                    v___x_1701_ = v___x_1674_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1703_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___x_1699_);
                    v___x_1701_ = v_reuseFailAlloc_1703_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1702_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1702_, 0, v___x_1697_);
                leanh::lean_ctor_set(v___x_1702_, 1, v___x_1701_);
                return v___x_1702_;
            }
            8 => {
                if v_isShared_1679_ == 0 {
                    leanh::lean_ctor_set(v___x_1678_, 1, v___x_1712_);
                    v___x_1714_ = v___x_1678_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1718_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_fst_1676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1712_);
                    v___x_1714_ = v_reuseFailAlloc_1718_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1675_ == 0 {
                    leanh::lean_ctor_set(v___x_1674_, 1, v___x_1714_);
                    leanh::lean_ctor_set(v___x_1674_, 0, v___x_1710_);
                    v___x_1716_ = v___x_1674_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1714_);
                    v___x_1716_ = v_reuseFailAlloc_1717_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1716_;
            }
            11 => {
                if v___y_1721_ == 0 {
                    state = 4;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_1683_);
                    leanh::lean_dec(v_snd_1681_);
                    leanh::lean_del_object(v___x_1678_);
                    leanh::lean_del_object(v___x_1674_);
                    v___x_1722_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1722_, 0, v_fst_1680_);
                    leanh::lean_ctor_set(v___x_1722_, 1, v___x_1688_);
                    v___x_1723_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1723_, 0, v_fst_1676_);
                    leanh::lean_ctor_set(v___x_1723_, 1, v___x_1722_);
                    v___x_1724_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1724_, 0, v_fst_1672_);
                    leanh::lean_ctor_set(v___x_1724_, 1, v___x_1723_);
                    v_a_1669_ = v___x_1724_;
                    state = 0;
                    continue;
                }
            }
            12 => {
                if v_isShared_1679_ == 0 {
                    leanh::lean_ctor_set(v___x_1678_, 1, v___x_1729_);
                    v___x_1731_ = v___x_1678_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1735_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_fst_1676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1729_);
                    v___x_1731_ = v_reuseFailAlloc_1735_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_1675_ == 0 {
                    leanh::lean_ctor_set(v___x_1674_, 1, v___x_1731_);
                    v___x_1733_ = v___x_1674_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_fst_1672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 1, v___x_1731_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg___boxed(
    mut v_s_1742_: *mut leanh::LeanObject,
    mut v___x_1743_: *mut leanh::LeanObject,
    mut v___x_1744_: *mut leanh::LeanObject,
    mut v___x_1745_: *mut leanh::LeanObject,
    mut v_a_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2150__boxed_1747_: u32 = 0;
    let mut v_res_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2150__boxed_1747_ = leanh::lean_unbox_uint32(v___x_1745_);
    leanh::lean_dec(v___x_1745_);
    v_res_1748_ = l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_1742_, v___x_1743_, v___x_1744_, v___x_2150__boxed_1747_, v_a_1746_);
    leanh::lean_dec(v___x_1743_);
    leanh::lean_dec_ref(v_s_1742_);
    return v_res_1748_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v_scheme_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_scheme_1750_ = l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0;
    v___x_1751_ = lean_string_utf8_byte_size(v_scheme_1750_);
    return v___x_1751_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(
    mut v_s_1752_: *mut leanh::LeanObject,
    mut v_a_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v_fst_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: u8 = 0;
    let mut v_scheme_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u32 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v_fst_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1808_: u8 = 0;
    let mut v_unused_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v_unused_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1818_: u8 = 0;
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1754_ = leanh::lean_ctor_get(v_a_1753_, 1);
                v_fst_1755_ = leanh::lean_ctor_get(v_a_1753_, 0);
                v_isSharedCheck_1819_ = (!leanh::lean_is_exclusive(v_a_1753_)) as u8;
                if v_isSharedCheck_1819_ == 0 {
                    v___x_1757_ = v_a_1753_;
                    v_isShared_1758_ = v_isSharedCheck_1819_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1754_);
                    leanh::lean_inc(v_fst_1755_);
                    leanh::lean_dec(v_a_1753_);
                    v___x_1757_ = leanh::lean_box(0);
                    v_isShared_1758_ = v_isSharedCheck_1819_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1759_ = leanh::lean_ctor_get(v_snd_1754_, 0);
                v_snd_1760_ = leanh::lean_ctor_get(v_snd_1754_, 1);
                v_isSharedCheck_1818_ = (!leanh::lean_is_exclusive(v_snd_1754_)) as u8;
                if v_isSharedCheck_1818_ == 0 {
                    v___x_1762_ = v_snd_1754_;
                    v_isShared_1763_ = v_isSharedCheck_1818_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1760_);
                    leanh::lean_inc(v_fst_1759_);
                    leanh::lean_dec(v_snd_1754_);
                    v___x_1762_ = leanh::lean_box(0);
                    v_isShared_1763_ = v_isSharedCheck_1818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1764_ = lean_string_utf8_byte_size(v_s_1752_);
                v___x_1765_ = lean_nat_dec_eq(v_snd_1760_, v___x_1764_);
                if v___x_1765_ == 0 {
                    v_scheme_1766_ = l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__0;
                    v___x_1767_ = lean_string_utf8_get_fast(v_s_1752_, v_snd_1760_);
                    v___x_1768_ = lean_string_utf8_next_fast(v_s_1752_, v_snd_1760_);
                    v___x_1778_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg___closed__1);
                    v___x_1779_ = lean_nat_sub(v___x_1764_, v_snd_1760_);
                    v___x_1780_ = lean_nat_dec_le(v___x_1778_, v___x_1779_);
                    leanh::lean_dec(v___x_1779_);
                    if v___x_1780_ == 0 {
                        leanh::lean_dec(v_snd_1760_);
                        state = 3;
                        continue;
                    } else {
                        v___x_1781_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1782_ = lean_string_memcmp(
                            v_s_1752_,
                            v_scheme_1766_,
                            v_snd_1760_,
                            v___x_1781_,
                            v___x_1778_,
                        );
                        if v___x_1782_ == 0 {
                            leanh::lean_dec(v_snd_1760_);
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_1762_);
                            leanh::lean_del_object(v___x_1757_);
                            leanh::lean_inc(v_snd_1760_);
                            leanh::lean_inc_ref(v_s_1752_);
                            v___x_1783_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_1783_, 0, v_s_1752_);
                            leanh::lean_ctor_set(v___x_1783_, 1, v_snd_1760_);
                            leanh::lean_ctor_set(v___x_1783_, 2, v___x_1764_);
                            v___x_1784_ = l_String_Slice_pos_x21(v___x_1783_, v___x_1778_);
                            leanh::lean_dec_ref_known(v___x_1783_, 3);
                            v___x_1785_ = lean_nat_add(v_snd_1760_, v___x_1784_);
                            leanh::lean_dec(v___x_1784_);
                            leanh::lean_inc(v___x_1785_);
                            v___x_1786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1786_, 0, v___x_1768_);
                            leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                            v___x_1787_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1787_, 0, v_fst_1759_);
                            leanh::lean_ctor_set(v___x_1787_, 1, v___x_1786_);
                            v___x_1788_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1788_, 0, v_fst_1755_);
                            leanh::lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                            v___x_1789_ = l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_1752_, v___x_1785_, v_snd_1760_, v___x_1767_, v___x_1788_);
                            leanh::lean_dec(v___x_1785_);
                            v_snd_1790_ = leanh::lean_ctor_get(v___x_1789_, 1);
                            leanh::lean_inc(v_snd_1790_);
                            v_snd_1791_ = leanh::lean_ctor_get(v_snd_1790_, 1);
                            leanh::lean_inc(v_snd_1791_);
                            v_fst_1792_ = leanh::lean_ctor_get(v___x_1789_, 0);
                            leanh::lean_inc(v_fst_1792_);
                            leanh::lean_dec_ref(v___x_1789_);
                            v_fst_1793_ = leanh::lean_ctor_get(v_snd_1790_, 0);
                            v_isSharedCheck_1810_ =
                                (!leanh::lean_is_exclusive(v_snd_1790_)) as u8;
                            if v_isSharedCheck_1810_ == 0 {
                                v_unused_1811_ = leanh::lean_ctor_get(v_snd_1790_, 1);
                                leanh::lean_dec(v_unused_1811_);
                                v___x_1795_ = v_snd_1790_;
                                v_isShared_1796_ = v_isSharedCheck_1810_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_fst_1793_);
                                leanh::lean_dec(v_snd_1790_);
                                v___x_1795_ = leanh::lean_box(0);
                                v_isShared_1796_ = v_isSharedCheck_1810_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_s_1752_);
                    if v_isShared_1763_ == 0 {
                        v___x_1813_ = v___x_1762_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_fst_1759_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_snd_1760_);
                        v___x_1813_ = v_reuseFailAlloc_1817_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1770_ = lean_string_push(v_fst_1755_, v___x_1767_);
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 1, v___x_1768_);
                    v___x_1772_ = v___x_1762_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1777_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_fst_1759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___x_1768_);
                    v___x_1772_ = v_reuseFailAlloc_1777_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1758_ == 0 {
                    leanh::lean_ctor_set(v___x_1757_, 1, v___x_1772_);
                    leanh::lean_ctor_set(v___x_1757_, 0, v___x_1770_);
                    v___x_1774_ = v___x_1757_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1776_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 1, v___x_1772_);
                    v___x_1774_ = v_reuseFailAlloc_1776_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_1753_ = v___x_1774_;
                state = 0;
                continue;
            }
            6 => {
                v_fst_1797_ = leanh::lean_ctor_get(v_snd_1791_, 0);
                v_isSharedCheck_1808_ = (!leanh::lean_is_exclusive(v_snd_1791_)) as u8;
                if v_isSharedCheck_1808_ == 0 {
                    v_unused_1809_ = leanh::lean_ctor_get(v_snd_1791_, 1);
                    leanh::lean_dec(v_unused_1809_);
                    v___x_1799_ = v_snd_1791_;
                    v_isShared_1800_ = v_isSharedCheck_1808_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_1797_);
                    leanh::lean_dec(v_snd_1791_);
                    v___x_1799_ = leanh::lean_box(0);
                    v_isShared_1800_ = v_isSharedCheck_1808_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1800_ == 0 {
                    leanh::lean_ctor_set(v___x_1799_, 1, v_fst_1797_);
                    leanh::lean_ctor_set(v___x_1799_, 0, v_fst_1793_);
                    v___x_1802_ = v___x_1799_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_fst_1793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_fst_1797_);
                    v___x_1802_ = v_reuseFailAlloc_1807_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1796_ == 0 {
                    leanh::lean_ctor_set(v___x_1795_, 1, v___x_1802_);
                    leanh::lean_ctor_set(v___x_1795_, 0, v_fst_1792_);
                    v___x_1804_ = v___x_1795_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_fst_1792_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1802_);
                    v___x_1804_ = v_reuseFailAlloc_1806_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_1753_ = v___x_1804_;
                state = 0;
                continue;
            }
            10 => {
                if v_isShared_1758_ == 0 {
                    leanh::lean_ctor_set(v___x_1757_, 1, v___x_1813_);
                    v___x_1815_ = v___x_1757_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1816_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_fst_1755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1813_);
                    v___x_1815_ = v_reuseFailAlloc_1816_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_rewriteManualLinksCore(
    mut v_s_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1836_: u8 = 0;
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v_unused_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1829_ = l_Lean_rewriteManualLinksCore___closed__2;
                v___x_1830_ = l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_1828_, v___x_1829_);
                v_snd_1831_ = leanh::lean_ctor_get(v___x_1830_, 1);
                leanh::lean_inc(v_snd_1831_);
                v_fst_1832_ = leanh::lean_ctor_get(v___x_1830_, 0);
                leanh::lean_inc(v_fst_1832_);
                leanh::lean_dec_ref(v___x_1830_);
                v_fst_1833_ = leanh::lean_ctor_get(v_snd_1831_, 0);
                v_isSharedCheck_1840_ = (!leanh::lean_is_exclusive(v_snd_1831_)) as u8;
                if v_isSharedCheck_1840_ == 0 {
                    v_unused_1841_ = leanh::lean_ctor_get(v_snd_1831_, 1);
                    leanh::lean_dec(v_unused_1841_);
                    v___x_1835_ = v_snd_1831_;
                    v_isShared_1836_ = v_isSharedCheck_1840_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_1833_);
                    leanh::lean_dec(v_snd_1831_);
                    v___x_1835_ = leanh::lean_box(0);
                    v_isShared_1836_ = v_isSharedCheck_1840_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1836_ == 0 {
                    leanh::lean_ctor_set(v___x_1835_, 1, v_fst_1832_);
                    v___x_1838_ = v___x_1835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1839_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_fst_1833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_fst_1832_);
                    v___x_1838_ = v_reuseFailAlloc_1839_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__0(
    mut v_s_1842_: *mut leanh::LeanObject,
    mut v___x_1843_: *mut leanh::LeanObject,
    mut v___x_1844_: *mut leanh::LeanObject,
    mut v___x_1845_: u32,
    mut v_inst_1846_: *mut leanh::LeanObject,
    mut v_a_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__0___redArg(v_s_1842_, v___x_1843_, v___x_1844_, v___x_1845_, v_a_1847_);
    return v___x_1848_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__0___boxed(
    mut v_s_1849_: *mut leanh::LeanObject,
    mut v___x_1850_: *mut leanh::LeanObject,
    mut v___x_1851_: *mut leanh::LeanObject,
    mut v___x_1852_: *mut leanh::LeanObject,
    mut v_inst_1853_: *mut leanh::LeanObject,
    mut v_a_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2435__boxed_1855_: u32 = 0;
    let mut v_res_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2435__boxed_1855_ = leanh::lean_unbox_uint32(v___x_1852_);
    leanh::lean_dec(v___x_1852_);
    v_res_1856_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__0(
            v_s_1849_,
            v___x_1850_,
            v___x_1851_,
            v___x_2435__boxed_1855_,
            v_inst_1853_,
            v_a_1854_,
        );
    leanh::lean_dec(v___x_1850_);
    leanh::lean_dec_ref(v_s_1849_);
    return v_res_1856_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1(
    mut v_s_1857_: *mut leanh::LeanObject,
    mut v_inst_1858_: *mut leanh::LeanObject,
    mut v_a_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1860_ = l___private_Init_While_0__whileM_erased___at___00Lean_rewriteManualLinksCore_spec__1___redArg(v_s_1857_, v_a_1859_);
    return v___x_1860_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(
    mut v_docString_1864_: *mut leanh::LeanObject,
    mut v_a_1865_: *mut leanh::LeanObject,
    mut v_a_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1873_: u8 = 0;
    let mut v_snd_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1889_: u8 = 0;
    let mut v_unused_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1865_) == 0 {
                    v___x_1867_ = l_List_reverse___redArg(v_a_1866_);
                    return v___x_1867_;
                } else {
                    v_head_1868_ = leanh::lean_ctor_get(v_a_1865_, 0);
                    leanh::lean_inc(v_head_1868_);
                    v_fst_1869_ = leanh::lean_ctor_get(v_head_1868_, 0);
                    leanh::lean_inc(v_fst_1869_);
                    v_tail_1870_ = leanh::lean_ctor_get(v_a_1865_, 1);
                    v_isSharedCheck_1889_ = (!leanh::lean_is_exclusive(v_a_1865_)) as u8;
                    if v_isSharedCheck_1889_ == 0 {
                        v_unused_1890_ = leanh::lean_ctor_get(v_a_1865_, 0);
                        leanh::lean_dec(v_unused_1890_);
                        v___x_1872_ = v_a_1865_;
                        v_isShared_1873_ = v_isSharedCheck_1889_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1870_);
                        leanh::lean_dec(v_a_1865_);
                        v___x_1872_ = leanh::lean_box(0);
                        v_isShared_1873_ = v_isSharedCheck_1889_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1874_ = leanh::lean_ctor_get(v_head_1868_, 1);
                leanh::lean_inc(v_snd_1874_);
                leanh::lean_dec(v_head_1868_);
                v_start_1875_ = leanh::lean_ctor_get(v_fst_1869_, 0);
                leanh::lean_inc(v_start_1875_);
                v_stop_1876_ = leanh::lean_ctor_get(v_fst_1869_, 1);
                leanh::lean_inc(v_stop_1876_);
                leanh::lean_dec(v_fst_1869_);
                v___x_1877_ =
                    l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__0;
                v___x_1878_ =
                    lean_string_utf8_extract(v_docString_1864_, v_start_1875_, v_stop_1876_);
                leanh::lean_dec(v_stop_1876_);
                leanh::lean_dec(v_start_1875_);
                v___x_1879_ = lean_string_append(v___x_1877_, v___x_1878_);
                leanh::lean_dec_ref(v___x_1878_);
                v___x_1880_ =
                    l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__1;
                v___x_1881_ = lean_string_append(v___x_1879_, v___x_1880_);
                v___x_1882_ = lean_string_append(v___x_1881_, v_snd_1874_);
                leanh::lean_dec(v_snd_1874_);
                v___x_1883_ =
                    l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2;
                v___x_1884_ = lean_string_append(v___x_1882_, v___x_1883_);
                if v_isShared_1873_ == 0 {
                    leanh::lean_ctor_set(v___x_1872_, 1, v_a_1866_);
                    leanh::lean_ctor_set(v___x_1872_, 0, v___x_1884_);
                    v___x_1886_ = v___x_1872_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1888_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_a_1866_);
                    v___x_1886_ = v_reuseFailAlloc_1888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1865_ = v_tail_1870_;
                v_a_1866_ = v___x_1886_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___boxed(
    mut v_docString_1891_: *mut leanh::LeanObject,
    mut v_a_1892_: *mut leanh::LeanObject,
    mut v_a_1893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(
        v_docString_1891_,
        v_a_1892_,
        v_a_1893_,
    );
    leanh::lean_dec_ref(v_docString_1891_);
    return v_res_1894_;
}
pub unsafe fn l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(
    mut v_x_1895_: *mut leanh::LeanObject,
    mut v_x_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1896_) == 0 {
                    return v_x_1895_;
                } else {
                    v_head_1897_ = leanh::lean_ctor_get(v_x_1896_, 0);
                    v_tail_1898_ = leanh::lean_ctor_get(v_x_1896_, 1);
                    v___x_1899_ = lean_string_append(v_x_1895_, v_head_1897_);
                    v_x_1895_ = v___x_1899_;
                    v_x_1896_ = v_tail_1898_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_rewriteManualLinks_spec__1___boxed(
    mut v_x_1901_: *mut leanh::LeanObject,
    mut v_x_1902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1903_ = l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v_x_1901_, v_x_1902_);
    leanh::lean_dec(v_x_1902_);
    return v_res_1903_;
}
pub unsafe fn l_Lean_rewriteManualLinks(
    mut v_docString_1905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    leanh::lean_inc_ref(v_docString_1905_);
    v___x_1907_ = l_Lean_rewriteManualLinksCore(v_docString_1905_);
    v_fst_1908_ = leanh::lean_ctor_get(v___x_1907_, 0);
    leanh::lean_inc(v_fst_1908_);
    v_snd_1909_ = leanh::lean_ctor_get(v___x_1907_, 1);
    leanh::lean_inc(v_snd_1909_);
    leanh::lean_dec_ref(v___x_1907_);
    v___x_1910_ = lean_array_get_size(v_fst_1908_);
    v___x_1911_ = leanh::lean_unsigned_to_nat(0);
    v___x_1912_ = lean_nat_dec_eq(v___x_1910_, v___x_1911_);
    if v___x_1912_ == 0 {
        let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1913_ = l_Lean_rewriteManualLinks___closed__0;
        v___x_1914_ = lean_array_to_list(v_fst_1908_);
        v___x_1915_ = leanh::lean_box(0);
        v___x_1916_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0(
            v_docString_1905_,
            v___x_1914_,
            v___x_1915_,
        );
        leanh::lean_dec_ref(v_docString_1905_);
        v___x_1917_ = l___private_Lean_DocString_Links_0__Lean_rw___closed__7;
        v___x_1918_ =
            l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_1917_, v___x_1916_);
        leanh::lean_dec(v___x_1916_);
        v___x_1919_ = lean_string_append(v___x_1913_, v___x_1918_);
        leanh::lean_dec_ref(v___x_1918_);
        v___x_1920_ = l_List_mapTR_loop___at___00Lean_rewriteManualLinks_spec__0___closed__2;
        v___x_1921_ = lean_string_append(v_snd_1909_, v___x_1920_);
        v___x_1922_ = lean_string_append(v___x_1921_, v___x_1919_);
        leanh::lean_dec_ref(v___x_1919_);
        return v___x_1922_;
    } else {
        leanh::lean_dec(v_fst_1908_);
        leanh::lean_dec_ref(v_docString_1905_);
        return v_snd_1909_;
    }
}
pub unsafe fn l_Lean_rewriteManualLinks___boxed(
    mut v_docString_1923_: *mut leanh::LeanObject,
    mut v_a_1924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1925_ = l_Lean_rewriteManualLinks(v_docString_1923_);
    return v_res_1925_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(
    mut v_docString_1929_: *mut leanh::LeanObject,
    mut v_a_1930_: *mut leanh::LeanObject,
    mut v_a_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1938_: u8 = 0;
    let mut v_snd_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_unused_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1930_) == 0 {
                    v___x_1932_ = l_List_reverse___redArg(v_a_1931_);
                    return v___x_1932_;
                } else {
                    v_head_1933_ = leanh::lean_ctor_get(v_a_1930_, 0);
                    leanh::lean_inc(v_head_1933_);
                    v_fst_1934_ = leanh::lean_ctor_get(v_head_1933_, 0);
                    leanh::lean_inc(v_fst_1934_);
                    v_tail_1935_ = leanh::lean_ctor_get(v_a_1930_, 1);
                    v_isSharedCheck_1959_ = (!leanh::lean_is_exclusive(v_a_1930_)) as u8;
                    if v_isSharedCheck_1959_ == 0 {
                        v_unused_1960_ = leanh::lean_ctor_get(v_a_1930_, 0);
                        leanh::lean_dec(v_unused_1960_);
                        v___x_1937_ = v_a_1930_;
                        v_isShared_1938_ = v_isSharedCheck_1959_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1935_);
                        leanh::lean_dec(v_a_1930_);
                        v___x_1937_ = leanh::lean_box(0);
                        v_isShared_1938_ = v_isSharedCheck_1959_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1939_ = leanh::lean_ctor_get(v_head_1933_, 1);
                leanh::lean_inc(v_snd_1939_);
                leanh::lean_dec(v_head_1933_);
                v_start_1940_ = leanh::lean_ctor_get(v_fst_1934_, 0);
                leanh::lean_inc(v_start_1940_);
                v_stop_1941_ = leanh::lean_ctor_get(v_fst_1934_, 1);
                leanh::lean_inc(v_stop_1941_);
                leanh::lean_dec(v_fst_1934_);
                v___x_1942_ =
                    l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__0;
                v___x_1943_ =
                    lean_string_utf8_extract(v_docString_1929_, v_start_1940_, v_stop_1941_);
                leanh::lean_dec(v_stop_1941_);
                leanh::lean_dec(v_start_1940_);
                v___x_1944_ = l_String_quote(v___x_1943_);
                v___x_1945_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1945_, 0, v___x_1944_);
                v___x_1946_ = l_Std_Format_defWidth;
                v___x_1947_ = leanh::lean_unsigned_to_nat(0);
                v___x_1948_ =
                    l_Std_Format_pretty(v___x_1945_, v___x_1946_, v___x_1947_, v___x_1947_);
                v___x_1949_ = lean_string_append(v___x_1942_, v___x_1948_);
                leanh::lean_dec_ref(v___x_1948_);
                v___x_1950_ =
                    l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__1;
                v___x_1951_ = lean_string_append(v___x_1949_, v___x_1950_);
                v___x_1952_ = lean_string_append(v___x_1951_, v_snd_1939_);
                leanh::lean_dec(v_snd_1939_);
                v___x_1953_ =
                    l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___closed__2;
                v___x_1954_ = lean_string_append(v___x_1952_, v___x_1953_);
                if v_isShared_1938_ == 0 {
                    leanh::lean_ctor_set(v___x_1937_, 1, v_a_1931_);
                    leanh::lean_ctor_set(v___x_1937_, 0, v___x_1954_);
                    v___x_1956_ = v___x_1937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_a_1931_);
                    v___x_1956_ = v_reuseFailAlloc_1958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1930_ = v_tail_1935_;
                v_a_1931_ = v___x_1956_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0___boxed(
    mut v_docString_1961_: *mut leanh::LeanObject,
    mut v_a_1962_: *mut leanh::LeanObject,
    mut v_a_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(
        v_docString_1961_,
        v_a_1962_,
        v_a_1963_,
    );
    leanh::lean_dec_ref(v_docString_1961_);
    return v_res_1964_;
}
pub unsafe fn l_Lean_validateBuiltinDocString(
    mut v_docString_1966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: u8 = 0;
    leanh::lean_inc_ref(v_docString_1966_);
    v___x_1968_ = l_Lean_rewriteManualLinksCore(v_docString_1966_);
    v_fst_1969_ = leanh::lean_ctor_get(v___x_1968_, 0);
    leanh::lean_inc(v_fst_1969_);
    leanh::lean_dec_ref(v___x_1968_);
    v___x_1970_ = lean_array_get_size(v_fst_1969_);
    v___x_1971_ = leanh::lean_unsigned_to_nat(0);
    v___x_1972_ = lean_nat_dec_eq(v___x_1970_, v___x_1971_);
    if v___x_1972_ == 0 {
        let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1973_ = l_Lean_validateBuiltinDocString___closed__0;
        v___x_1974_ = lean_array_to_list(v_fst_1969_);
        v___x_1975_ = leanh::lean_box(0);
        v___x_1976_ = l_List_mapTR_loop___at___00Lean_validateBuiltinDocString_spec__0(
            v_docString_1966_,
            v___x_1974_,
            v___x_1975_,
        );
        leanh::lean_dec_ref(v_docString_1966_);
        v___x_1977_ = l___private_Lean_DocString_Links_0__Lean_rw___closed__7;
        v___x_1978_ =
            l_List_foldl___at___00Lean_rewriteManualLinks_spec__1(v___x_1977_, v___x_1976_);
        leanh::lean_dec(v___x_1976_);
        v___x_1979_ = lean_string_append(v___x_1973_, v___x_1978_);
        leanh::lean_dec_ref(v___x_1978_);
        v___x_1980_ = lean_mk_io_user_error(v___x_1979_);
        v___x_1981_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1981_, 0, v___x_1980_);
        return v___x_1981_;
    } else {
        let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fst_1969_);
        leanh::lean_dec_ref(v_docString_1966_);
        v___x_1982_ = leanh::lean_box(0);
        v___x_1983_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1983_, 0, v___x_1982_);
        return v___x_1983_;
    }
}
pub unsafe fn l_Lean_validateBuiltinDocString___boxed(
    mut v_docString_1984_: *mut leanh::LeanObject,
    mut v_a_1985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1986_ = l_Lean_validateBuiltinDocString(v_docString_1984_);
    return v_res_1986_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString_Links(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DocString_Links_0__Lean_initFn_00___x40_Lean_DocString_Links_3730308748____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_manualRoot = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_manualRoot);
    leanh::lean_dec_ref(res);
    l___private_Lean_DocString_Links_0__Lean_domainMap =
        _init_l___private_Lean_DocString_Links_0__Lean_domainMap();
    leanh::lean_mark_persistent(l___private_Lean_DocString_Links_0__Lean_domainMap);
    l_Lean_manualDomains = _init_l_Lean_manualDomains();
    leanh::lean_mark_persistent(l_Lean_manualDomains);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString_Links(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DocString_Links(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Links(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DocString_Links(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_DocString_Links(builtin);
}