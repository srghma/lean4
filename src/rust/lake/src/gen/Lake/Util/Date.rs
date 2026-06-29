// Lean compiler output
// Module: Lake.Util.Date
// Imports: Init.Data.Ord.Basic Lean.Data.Json Lake.Util.String Init.Data.String.Search Init.Data.Iterators.Consumers.Collect Init.Data.ToString.Macro
use crate::ffi::{
    lean_array_push, lean_array_to_list, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mod, lean_nat_sub, lean_nat_to_int, lean_string_append,
    lean_string_length, lean_string_utf8_byte_size, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_uint32_dec_eq,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toNat_x3f;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Lake::Util::String::{
    initialize_Lake_Util_String, l_Lake_zpad, runtime_initialize_Lake_Util_String,
};
use crate::r#gen::Lean::Data::Json::{
    initialize_Lean_Data_Json, runtime_initialize_Lean_Data_Json,
};
pub static l_Lake_instInhabitedDate_default___closed__0_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instInhabitedDate_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDate_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedDate_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDate_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedDate: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedDate_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instOrdDate___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instOrdDate_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instOrdDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdDate___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instOrdDate: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdDate___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [123, 32, 0],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [121, 101, 97, 114, 0],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprDate_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDate_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDate_repr___redArg___closed__8_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [44, 0],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__10_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [109, 111, 110, 116, 104, 0],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprDate_repr___redArg___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDate_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDate_repr___redArg___closed__13_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [100, 97, 121, 0],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__14_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprDate_repr___redArg___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDate_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDate_repr___redArg___closed__16_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [32, 125, 0],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprDate_repr___redArg___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDate_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprDate_repr___redArg___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprDate_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprDate_repr___redArg___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate_repr___redArg___closed__20_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprDate_repr___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprDate___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprDate_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprDate: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprDate___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Date_instLT: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Date_instLE: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Date_instMin___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Date_instMin___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Date_instMin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instMin___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Date_instMin: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instMin___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Date_instMax___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Date_instMax___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Date_instMax___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instMax___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Date_instMax: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instMax___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_Date_ofString_x3f___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_Date_ofString_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_ofString_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Date_fromJson_x3f___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 97, 116, 101, 0,
        ],
    };
static mut l_Lake_Date_fromJson_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_fromJson_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Date_fromJson_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Date_fromJson_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Date_fromJson_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_fromJson_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Date_instFromJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Date_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Date_instFromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Date_instFromJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Date_toString___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [45, 0],
    };
static mut l_Lake_Date_toString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_toString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Date_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Date_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Date_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Date_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Date_instToJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Date_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Date_instToJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instToJson___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Date_instToJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Date_instToJson___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_instDecidableEqDate_decEq(
    mut v_x_351_: *mut crate::leanh::LeanObject,
    mut v_x_352_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_year_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: u8 = 0;
    v_year_353_ = crate::leanh::lean_ctor_get(v_x_351_, 0);
    v_month_354_ = crate::leanh::lean_ctor_get(v_x_351_, 1);
    v_day_355_ = crate::leanh::lean_ctor_get(v_x_351_, 2);
    v_year_356_ = crate::leanh::lean_ctor_get(v_x_352_, 0);
    v_month_357_ = crate::leanh::lean_ctor_get(v_x_352_, 1);
    v_day_358_ = crate::leanh::lean_ctor_get(v_x_352_, 2);
    v___x_359_ = lean_nat_dec_eq(v_year_353_, v_year_356_);
    if v___x_359_ == 0 {
        return v___x_359_;
    } else {
        let mut v___x_360_: u8 = 0;
        v___x_360_ = lean_nat_dec_eq(v_month_354_, v_month_357_);
        if v___x_360_ == 0 {
            return v___x_360_;
        } else {
            let mut v___x_361_: u8 = 0;
            v___x_361_ = lean_nat_dec_eq(v_day_355_, v_day_358_);
            return v___x_361_;
        }
    }
}
pub unsafe fn l_Lake_instDecidableEqDate_decEq___boxed(
    mut v_x_362_: *mut crate::leanh::LeanObject,
    mut v_x_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_364_: u8 = 0;
    let mut v_r_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_364_ = l_Lake_instDecidableEqDate_decEq(v_x_362_, v_x_363_);
    crate::leanh::lean_dec_ref(v_x_363_);
    crate::leanh::lean_dec_ref(v_x_362_);
    v_r_365_ = crate::leanh::lean_box((v_res_364_) as usize);
    return v_r_365_;
}
pub unsafe fn l_Lake_instDecidableEqDate(
    mut v_x_366_: *mut crate::leanh::LeanObject,
    mut v_x_367_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_368_: u8 = 0;
    v___x_368_ = l_Lake_instDecidableEqDate_decEq(v_x_366_, v_x_367_);
    return v___x_368_;
}
pub unsafe fn l_Lake_instDecidableEqDate___boxed(
    mut v_x_369_: *mut crate::leanh::LeanObject,
    mut v_x_370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_371_: u8 = 0;
    let mut v_r_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_371_ = l_Lake_instDecidableEqDate(v_x_369_, v_x_370_);
    crate::leanh::lean_dec_ref(v_x_370_);
    crate::leanh::lean_dec_ref(v_x_369_);
    v_r_372_ = crate::leanh::lean_box((v_res_371_) as usize);
    return v_r_372_;
}
pub unsafe fn l_Lake_instOrdDate_ord(
    mut v_x_373_: *mut crate::leanh::LeanObject,
    mut v_x_374_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_year_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: u8 = 0;
    v_year_375_ = crate::leanh::lean_ctor_get(v_x_373_, 0);
    v_month_376_ = crate::leanh::lean_ctor_get(v_x_373_, 1);
    v_day_377_ = crate::leanh::lean_ctor_get(v_x_373_, 2);
    v_year_378_ = crate::leanh::lean_ctor_get(v_x_374_, 0);
    v_month_379_ = crate::leanh::lean_ctor_get(v_x_374_, 1);
    v_day_380_ = crate::leanh::lean_ctor_get(v_x_374_, 2);
    v___x_381_ = lean_nat_dec_lt(v_year_375_, v_year_378_);
    if v___x_381_ == 0 {
        let mut v___x_382_: u8 = 0;
        v___x_382_ = lean_nat_dec_eq(v_year_375_, v_year_378_);
        if v___x_382_ == 0 {
            let mut v___x_383_: u8 = 0;
            v___x_383_ = 2;
            return v___x_383_;
        } else {
            let mut v___x_384_: u8 = 0;
            v___x_384_ = lean_nat_dec_lt(v_month_376_, v_month_379_);
            if v___x_384_ == 0 {
                let mut v___x_385_: u8 = 0;
                v___x_385_ = lean_nat_dec_eq(v_month_376_, v_month_379_);
                if v___x_385_ == 0 {
                    let mut v___x_386_: u8 = 0;
                    v___x_386_ = 2;
                    return v___x_386_;
                } else {
                    let mut v___x_387_: u8 = 0;
                    v___x_387_ = lean_nat_dec_lt(v_day_377_, v_day_380_);
                    if v___x_387_ == 0 {
                        let mut v___x_388_: u8 = 0;
                        v___x_388_ = lean_nat_dec_eq(v_day_377_, v_day_380_);
                        if v___x_388_ == 0 {
                            let mut v___x_389_: u8 = 0;
                            v___x_389_ = 2;
                            return v___x_389_;
                        } else {
                            let mut v___x_390_: u8 = 0;
                            v___x_390_ = 1;
                            return v___x_390_;
                        }
                    } else {
                        let mut v___x_391_: u8 = 0;
                        v___x_391_ = 0;
                        return v___x_391_;
                    }
                }
            } else {
                let mut v___x_392_: u8 = 0;
                v___x_392_ = 0;
                return v___x_392_;
            }
        }
    } else {
        let mut v___x_393_: u8 = 0;
        v___x_393_ = 0;
        return v___x_393_;
    }
}
pub unsafe fn l_Lake_instOrdDate_ord___boxed(
    mut v_x_394_: *mut crate::leanh::LeanObject,
    mut v_x_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_396_: u8 = 0;
    let mut v_r_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_396_ = l_Lake_instOrdDate_ord(v_x_394_, v_x_395_);
    crate::leanh::lean_dec_ref(v_x_395_);
    crate::leanh::lean_dec_ref(v_x_394_);
    v_r_397_ = crate::leanh::lean_box((v_res_396_) as usize);
    return v_r_397_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprDate_repr_spec__0(
    mut v_a_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = lean_nat_to_int(v_a_400_);
    return v___x_401_;
}
pub unsafe fn _init_l_Lake_instReprDate_repr___redArg___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_415_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_416_ = lean_nat_to_int(v___x_415_);
    return v___x_416_;
}
pub unsafe fn _init_l_Lake_instReprDate_repr___redArg___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_424_ = lean_nat_to_int(v___x_423_);
    return v___x_424_;
}
pub unsafe fn _init_l_Lake_instReprDate_repr___redArg___closed__15() -> *mut crate::leanh::LeanObject
{
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_429_ = lean_nat_to_int(v___x_428_);
    return v___x_429_;
}
pub unsafe fn _init_l_Lake_instReprDate_repr___redArg___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = l_Lake_instReprDate_repr___redArg___closed__0;
    v___x_432_ = lean_string_length(v___x_431_);
    return v___x_432_;
}
pub unsafe fn _init_l_Lake_instReprDate_repr___redArg___closed__18() -> *mut crate::leanh::LeanObject
{
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__17_once),
        _init_l_Lake_instReprDate_repr___redArg___closed__17,
    );
    v___x_434_ = lean_nat_to_int(v___x_433_);
    return v___x_434_;
}
pub unsafe fn l_Lake_instReprDate_repr___redArg(
    mut v_x_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: u8 = 0;
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_year_440_ = crate::leanh::lean_ctor_get(v_x_439_, 0);
    crate::leanh::lean_inc(v_year_440_);
    v_month_441_ = crate::leanh::lean_ctor_get(v_x_439_, 1);
    crate::leanh::lean_inc(v_month_441_);
    v_day_442_ = crate::leanh::lean_ctor_get(v_x_439_, 2);
    crate::leanh::lean_inc(v_day_442_);
    crate::leanh::lean_dec_ref(v_x_439_);
    v___x_443_ = l_Lake_instReprDate_repr___redArg___closed__5;
    v___x_444_ = l_Lake_instReprDate_repr___redArg___closed__6;
    v___x_445_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__7_once),
        _init_l_Lake_instReprDate_repr___redArg___closed__7,
    );
    v___x_446_ = l_Nat_reprFast(v_year_440_);
    v___x_447_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_447_, 0, v___x_446_);
    v___x_448_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_448_, 0, v___x_445_);
    crate::leanh::lean_ctor_set(v___x_448_, 1, v___x_447_);
    v___x_449_ = 0;
    v___x_450_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_450_, 0, v___x_448_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_450_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_449_,
    );
    v___x_451_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_451_, 0, v___x_444_);
    crate::leanh::lean_ctor_set(v___x_451_, 1, v___x_450_);
    v___x_452_ = l_Lake_instReprDate_repr___redArg___closed__9;
    v___x_453_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_453_, 0, v___x_451_);
    crate::leanh::lean_ctor_set(v___x_453_, 1, v___x_452_);
    v___x_454_ = crate::leanh::lean_box(1);
    v___x_455_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_455_, 0, v___x_453_);
    crate::leanh::lean_ctor_set(v___x_455_, 1, v___x_454_);
    v___x_456_ = l_Lake_instReprDate_repr___redArg___closed__11;
    v___x_457_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_457_, 0, v___x_455_);
    crate::leanh::lean_ctor_set(v___x_457_, 1, v___x_456_);
    v___x_458_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_458_, 0, v___x_457_);
    crate::leanh::lean_ctor_set(v___x_458_, 1, v___x_443_);
    v___x_459_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__12_once),
        _init_l_Lake_instReprDate_repr___redArg___closed__12,
    );
    v___x_460_ = l_Nat_reprFast(v_month_441_);
    v___x_461_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_461_, 0, v___x_460_);
    v___x_462_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_462_, 0, v___x_459_);
    crate::leanh::lean_ctor_set(v___x_462_, 1, v___x_461_);
    v___x_463_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_463_, 0, v___x_462_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_463_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_449_,
    );
    v___x_464_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_464_, 0, v___x_458_);
    crate::leanh::lean_ctor_set(v___x_464_, 1, v___x_463_);
    v___x_465_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_465_, 0, v___x_464_);
    crate::leanh::lean_ctor_set(v___x_465_, 1, v___x_452_);
    v___x_466_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_466_, 0, v___x_465_);
    crate::leanh::lean_ctor_set(v___x_466_, 1, v___x_454_);
    v___x_467_ = l_Lake_instReprDate_repr___redArg___closed__14;
    v___x_468_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_468_, 0, v___x_466_);
    crate::leanh::lean_ctor_set(v___x_468_, 1, v___x_467_);
    v___x_469_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_469_, 0, v___x_468_);
    crate::leanh::lean_ctor_set(v___x_469_, 1, v___x_443_);
    v___x_470_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__15_once),
        _init_l_Lake_instReprDate_repr___redArg___closed__15,
    );
    v___x_471_ = l_Nat_reprFast(v_day_442_);
    v___x_472_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_472_, 0, v___x_471_);
    v___x_473_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_473_, 0, v___x_470_);
    crate::leanh::lean_ctor_set(v___x_473_, 1, v___x_472_);
    v___x_474_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_474_, 0, v___x_473_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_474_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_449_,
    );
    v___x_475_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_475_, 0, v___x_469_);
    crate::leanh::lean_ctor_set(v___x_475_, 1, v___x_474_);
    v___x_476_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lake_instReprDate_repr___redArg___closed__18_once),
        _init_l_Lake_instReprDate_repr___redArg___closed__18,
    );
    v___x_477_ = l_Lake_instReprDate_repr___redArg___closed__19;
    v___x_478_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_478_, 0, v___x_477_);
    crate::leanh::lean_ctor_set(v___x_478_, 1, v___x_475_);
    v___x_479_ = l_Lake_instReprDate_repr___redArg___closed__20;
    v___x_480_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_480_, 0, v___x_478_);
    crate::leanh::lean_ctor_set(v___x_480_, 1, v___x_479_);
    v___x_481_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_481_, 0, v___x_476_);
    crate::leanh::lean_ctor_set(v___x_481_, 1, v___x_480_);
    v___x_482_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_482_, 0, v___x_481_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_482_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_449_,
    );
    return v___x_482_;
}
pub unsafe fn l_Lake_instReprDate_repr(
    mut v_x_483_: *mut crate::leanh::LeanObject,
    mut v_prec_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = l_Lake_instReprDate_repr___redArg(v_x_483_);
    return v___x_485_;
}
pub unsafe fn l_Lake_instReprDate_repr___boxed(
    mut v_x_486_: *mut crate::leanh::LeanObject,
    mut v_prec_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_488_ = l_Lake_instReprDate_repr(v_x_486_, v_prec_487_);
    crate::leanh::lean_dec(v_prec_487_);
    return v_res_488_;
}
pub unsafe fn _init_l_Lake_Date_instLT() -> *mut crate::leanh::LeanObject {
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_491_ = crate::leanh::lean_box(0);
    return v___x_491_;
}
pub unsafe fn _init_l_Lake_Date_instLE() -> *mut crate::leanh::LeanObject {
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = crate::leanh::lean_box(0);
    return v___x_492_;
}
pub unsafe fn l_Lake_Date_instMin___lam__0(
    mut v_x_493_: *mut crate::leanh::LeanObject,
    mut v_y_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_495_: u8 = 0;
    v___x_495_ = l_Lake_instOrdDate_ord(v_x_493_, v_y_494_);
    if v___x_495_ == 2 {
        crate::leanh::lean_inc_ref(v_y_494_);
        return v_y_494_;
    } else {
        crate::leanh::lean_inc_ref(v_x_493_);
        return v_x_493_;
    }
}
pub unsafe fn l_Lake_Date_instMin___lam__0___boxed(
    mut v_x_496_: *mut crate::leanh::LeanObject,
    mut v_y_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_498_ = l_Lake_Date_instMin___lam__0(v_x_496_, v_y_497_);
    crate::leanh::lean_dec_ref(v_y_497_);
    crate::leanh::lean_dec_ref(v_x_496_);
    return v_res_498_;
}
pub unsafe fn l_Lake_Date_instMax___lam__0(
    mut v_x_501_: *mut crate::leanh::LeanObject,
    mut v_y_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_503_: u8 = 0;
    v___x_503_ = l_Lake_instOrdDate_ord(v_x_501_, v_y_502_);
    if v___x_503_ == 2 {
        crate::leanh::lean_inc_ref(v_x_501_);
        return v_x_501_;
    } else {
        crate::leanh::lean_inc_ref(v_y_502_);
        return v_y_502_;
    }
}
pub unsafe fn l_Lake_Date_instMax___lam__0___boxed(
    mut v_x_504_: *mut crate::leanh::LeanObject,
    mut v_y_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_506_ = l_Lake_Date_instMax___lam__0(v_x_504_, v_y_505_);
    crate::leanh::lean_dec_ref(v_y_505_);
    crate::leanh::lean_dec_ref(v_x_504_);
    return v_res_506_;
}
pub unsafe fn l_Lake_Date_maxDay(
    mut v_y_509_: *mut crate::leanh::LeanObject,
    mut v_m_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: u8 = 0;
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: u8 = 0;
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: u8 = 0;
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: u8 = 0;
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: u8 = 0;
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_511_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_512_ = lean_nat_dec_eq(v_m_510_, v___x_511_);
                if v___x_512_ == 0 {
                    v___x_513_ = crate::leanh::lean_unsigned_to_nat(7);
                    v___x_514_ = lean_nat_dec_le(v_m_510_, v___x_513_);
                    if v___x_514_ == 0 {
                        v___x_515_ = crate::leanh::lean_unsigned_to_nat(31);
                        v___x_516_ = lean_nat_mod(v_m_510_, v___x_511_);
                        v___x_517_ = lean_nat_sub(v___x_515_, v___x_516_);
                        crate::leanh::lean_dec(v___x_516_);
                        return v___x_517_;
                    } else {
                        v___x_518_ = crate::leanh::lean_unsigned_to_nat(30);
                        v___x_519_ = lean_nat_mod(v_m_510_, v___x_511_);
                        v___x_520_ = lean_nat_add(v___x_518_, v___x_519_);
                        crate::leanh::lean_dec(v___x_519_);
                        return v___x_520_;
                    }
                } else {
                    v___x_521_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_522_ = lean_nat_mod(v_y_509_, v___x_521_);
                    v___x_523_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_530_ = lean_nat_dec_eq(v___x_522_, v___x_523_);
                    crate::leanh::lean_dec(v___x_522_);
                    if v___x_530_ == 0 {
                        v___x_531_ = crate::leanh::lean_unsigned_to_nat(28);
                        return v___x_531_;
                    } else {
                        v___x_532_ = crate::leanh::lean_unsigned_to_nat(100);
                        v___x_533_ = lean_nat_mod(v_y_509_, v___x_532_);
                        v___x_534_ = lean_nat_dec_eq(v___x_533_, v___x_523_);
                        crate::leanh::lean_dec(v___x_533_);
                        if v___x_534_ == 0 {
                            if v___x_530_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_535_ = crate::leanh::lean_unsigned_to_nat(29);
                                return v___x_535_;
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_525_ = crate::leanh::lean_unsigned_to_nat(400);
                v___x_526_ = lean_nat_mod(v_y_509_, v___x_525_);
                v___x_527_ = lean_nat_dec_eq(v___x_526_, v___x_523_);
                crate::leanh::lean_dec(v___x_526_);
                if v___x_527_ == 0 {
                    v___x_528_ = crate::leanh::lean_unsigned_to_nat(28);
                    return v___x_528_;
                } else {
                    v___x_529_ = crate::leanh::lean_unsigned_to_nat(29);
                    return v___x_529_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Date_maxDay___boxed(
    mut v_y_536_: *mut crate::leanh::LeanObject,
    mut v_m_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Lake_Date_maxDay(v_y_536_, v_m_537_);
    crate::leanh::lean_dec(v_m_537_);
    crate::leanh::lean_dec(v_y_536_);
    return v_res_538_;
}
pub unsafe fn l_Lake_Date_ofValid_x3f(
    mut v_year_539_: *mut crate::leanh::LeanObject,
    mut v_month_540_: *mut crate::leanh::LeanObject,
    mut v_day_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u8 = 0;
    v___x_542_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_543_ = lean_nat_dec_le(v___x_542_, v_month_540_);
    if v___x_543_ == 0 {
        let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_day_541_);
        crate::leanh::lean_dec(v_month_540_);
        crate::leanh::lean_dec(v_year_539_);
        v___x_544_ = crate::leanh::lean_box(0);
        return v___x_544_;
    } else {
        let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_546_: u8 = 0;
        v___x_545_ = crate::leanh::lean_unsigned_to_nat(12);
        v___x_546_ = lean_nat_dec_le(v_month_540_, v___x_545_);
        if v___x_546_ == 0 {
            let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_day_541_);
            crate::leanh::lean_dec(v_month_540_);
            crate::leanh::lean_dec(v_year_539_);
            v___x_547_ = crate::leanh::lean_box(0);
            return v___x_547_;
        } else {
            let mut v___x_548_: u8 = 0;
            v___x_548_ = lean_nat_dec_le(v___x_542_, v_day_541_);
            if v___x_548_ == 0 {
                let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_day_541_);
                crate::leanh::lean_dec(v_month_540_);
                crate::leanh::lean_dec(v_year_539_);
                v___x_549_ = crate::leanh::lean_box(0);
                return v___x_549_;
            } else {
                let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_551_: u8 = 0;
                v___x_550_ = l_Lake_Date_maxDay(v_year_539_, v_month_540_);
                v___x_551_ = lean_nat_dec_le(v_day_541_, v___x_550_);
                crate::leanh::lean_dec(v___x_550_);
                if v___x_551_ == 0 {
                    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_day_541_);
                    crate::leanh::lean_dec(v_month_540_);
                    crate::leanh::lean_dec(v_year_539_);
                    v___x_552_ = crate::leanh::lean_box(0);
                    return v___x_552_;
                } else {
                    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_553_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_553_, 0, v_year_539_);
                    crate::leanh::lean_ctor_set(v___x_553_, 1, v_month_540_);
                    crate::leanh::lean_ctor_set(v___x_553_, 2, v_day_541_);
                    v___x_554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_554_, 0, v___x_553_);
                    return v___x_554_;
                }
            }
        }
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0(
    mut v_s_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0;
    return v___x_558_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___boxed(
    mut v_s_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0(v_s_559_);
    crate::leanh::lean_dec_ref(v_s_559_);
    return v_res_560_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(
    mut v_t_561_: *mut crate::leanh::LeanObject,
    mut v___x_562_: *mut crate::leanh::LeanObject,
    mut v___x_563_: *mut crate::leanh::LeanObject,
    mut v_a_564_: *mut crate::leanh::LeanObject,
    mut v_b_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_577_: u8 = 0;
    let mut v_startInclusive_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: u32 = 0;
    let mut v___x_583_: u32 = 0;
    let mut v___x_584_: u8 = 0;
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_564_) == 0 {
                    v_currPos_573_ = crate::leanh::lean_ctor_get(v_a_564_, 0);
                    v_searcher_574_ = crate::leanh::lean_ctor_get(v_a_564_, 1);
                    v_isSharedCheck_600_ = (!crate::leanh::lean_is_exclusive(v_a_564_)) as u8;
                    if v_isSharedCheck_600_ == 0 {
                        v___x_576_ = v_a_564_;
                        v_isShared_577_ = v_isSharedCheck_600_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_574_);
                        crate::leanh::lean_inc(v_currPos_573_);
                        crate::leanh::lean_dec(v_a_564_);
                        v___x_576_ = crate::leanh::lean_box(0);
                        v_isShared_577_ = v_isSharedCheck_600_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_563_);
                    crate::leanh::lean_dec_ref(v_t_561_);
                    return v_b_565_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_t_561_);
                v___x_570_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_570_, 0, v_t_561_);
                crate::leanh::lean_ctor_set(v___x_570_, 1, v_startInclusive_568_);
                crate::leanh::lean_ctor_set(v___x_570_, 2, v_endExclusive_569_);
                v___x_571_ = lean_array_push(v_b_565_, v___x_570_);
                v_a_564_ = v_it_567_;
                v_b_565_ = v___x_571_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_578_ = crate::leanh::lean_ctor_get(v___x_562_, 1);
                v_endExclusive_579_ = crate::leanh::lean_ctor_get(v___x_562_, 2);
                v___x_580_ = lean_nat_sub(v_endExclusive_579_, v_startInclusive_578_);
                v___x_581_ = lean_nat_dec_eq(v_searcher_574_, v___x_580_);
                crate::leanh::lean_dec(v___x_580_);
                if v___x_581_ == 0 {
                    v___x_582_ = 45;
                    v___x_583_ = lean_string_utf8_get_fast(v_t_561_, v_searcher_574_);
                    v___x_584_ = lean_uint32_dec_eq(v___x_583_, v___x_582_);
                    if v___x_584_ == 0 {
                        v___x_585_ = lean_string_utf8_next_fast(v_t_561_, v_searcher_574_);
                        crate::leanh::lean_dec(v_searcher_574_);
                        if v_isShared_577_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_576_, 1, v___x_585_);
                            v___x_587_ = v___x_576_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_589_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_589_, 0, v_currPos_573_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_585_);
                            v___x_587_ = v_reuseFailAlloc_589_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_590_ = lean_string_utf8_next_fast(v_t_561_, v_searcher_574_);
                        v___x_591_ = lean_nat_sub(v___x_590_, v_searcher_574_);
                        v___x_592_ = lean_nat_add(v_searcher_574_, v___x_591_);
                        crate::leanh::lean_dec(v___x_591_);
                        v_slice_593_ = l_String_Slice_subslice_x21(
                            v___x_562_,
                            v_currPos_573_,
                            v_searcher_574_,
                        );
                        crate::leanh::lean_inc(v___x_592_);
                        if v_isShared_577_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_576_, 1, v___x_592_);
                            crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_592_);
                            v_nextIt_595_ = v___x_576_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_592_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_592_);
                            v_nextIt_595_ = v_reuseFailAlloc_598_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_576_);
                    crate::leanh::lean_dec(v_searcher_574_);
                    v___x_599_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_563_);
                    v_it_567_ = v___x_599_;
                    v_startInclusive_568_ = v_currPos_573_;
                    v_endExclusive_569_ = v___x_563_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_564_ = v___x_587_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_596_ = crate::leanh::lean_ctor_get(v_slice_593_, 0);
                crate::leanh::lean_inc(v_startInclusive_596_);
                v_endExclusive_597_ = crate::leanh::lean_ctor_get(v_slice_593_, 1);
                crate::leanh::lean_inc(v_endExclusive_597_);
                crate::leanh::lean_dec_ref(v_slice_593_);
                v_it_567_ = v_nextIt_595_;
                v_startInclusive_568_ = v_startInclusive_596_;
                v_endExclusive_569_ = v_endExclusive_597_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg___boxed(
    mut v_t_601_: *mut crate::leanh::LeanObject,
    mut v___x_602_: *mut crate::leanh::LeanObject,
    mut v___x_603_: *mut crate::leanh::LeanObject,
    mut v_a_604_: *mut crate::leanh::LeanObject,
    mut v_b_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_606_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(v_t_601_, v___x_602_, v___x_603_, v_a_604_, v_b_605_);
    crate::leanh::lean_dec_ref(v___x_602_);
    return v_res_606_;
}
pub unsafe fn l_Lake_Date_ofString_x3f(
    mut v_t_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_610_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_611_ = lean_string_utf8_byte_size(v_t_609_);
    crate::leanh::lean_inc_ref(v_t_609_);
    v___x_612_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_612_, 0, v_t_609_);
    crate::leanh::lean_ctor_set(v___x_612_, 1, v___x_610_);
    crate::leanh::lean_ctor_set(v___x_612_, 2, v___x_611_);
    v___x_613_ = l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0(v___x_612_);
    v___x_614_ = l_Lake_Date_ofString_x3f___closed__0;
    v___x_615_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(v_t_609_, v___x_612_, v___x_611_, v___x_613_, v___x_614_);
    crate::leanh::lean_dec_ref_known(v___x_612_, 3);
    v___x_616_ = lean_array_to_list(v___x_615_);
    if crate::leanh::lean_obj_tag(v___x_616_) == 1 {
        let mut v_tail_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_617_ = crate::leanh::lean_ctor_get(v___x_616_, 1);
        crate::leanh::lean_inc(v_tail_617_);
        if crate::leanh::lean_obj_tag(v_tail_617_) == 1 {
            let mut v_tail_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_tail_618_ = crate::leanh::lean_ctor_get(v_tail_617_, 1);
            crate::leanh::lean_inc(v_tail_618_);
            if crate::leanh::lean_obj_tag(v_tail_618_) == 1 {
                let mut v_tail_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_tail_619_ = crate::leanh::lean_ctor_get(v_tail_618_, 1);
                if crate::leanh::lean_obj_tag(v_tail_619_) == 0 {
                    let mut v_head_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_head_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_head_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_head_620_ = crate::leanh::lean_ctor_get(v___x_616_, 0);
                    crate::leanh::lean_inc(v_head_620_);
                    crate::leanh::lean_dec_ref_known(v___x_616_, 2);
                    v_head_621_ = crate::leanh::lean_ctor_get(v_tail_617_, 0);
                    crate::leanh::lean_inc(v_head_621_);
                    crate::leanh::lean_dec_ref_known(v_tail_617_, 2);
                    v_head_622_ = crate::leanh::lean_ctor_get(v_tail_618_, 0);
                    crate::leanh::lean_inc(v_head_622_);
                    crate::leanh::lean_dec_ref_known(v_tail_618_, 2);
                    v___x_623_ = l_String_Slice_toNat_x3f(v_head_620_);
                    crate::leanh::lean_dec(v_head_620_);
                    if crate::leanh::lean_obj_tag(v___x_623_) == 0 {
                        let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_head_622_);
                        crate::leanh::lean_dec(v_head_621_);
                        v___x_624_ = crate::leanh::lean_box(0);
                        return v___x_624_;
                    } else {
                        let mut v_val_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_val_625_ = crate::leanh::lean_ctor_get(v___x_623_, 0);
                        crate::leanh::lean_inc(v_val_625_);
                        crate::leanh::lean_dec_ref_known(v___x_623_, 1);
                        v___x_626_ = l_String_Slice_toNat_x3f(v_head_621_);
                        crate::leanh::lean_dec(v_head_621_);
                        if crate::leanh::lean_obj_tag(v___x_626_) == 0 {
                            let mut v___x_627_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_val_625_);
                            crate::leanh::lean_dec(v_head_622_);
                            v___x_627_ = crate::leanh::lean_box(0);
                            return v___x_627_;
                        } else {
                            let mut v_val_628_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_629_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v_val_628_ = crate::leanh::lean_ctor_get(v___x_626_, 0);
                            crate::leanh::lean_inc(v_val_628_);
                            crate::leanh::lean_dec_ref_known(v___x_626_, 1);
                            v___x_629_ = l_String_Slice_toNat_x3f(v_head_622_);
                            crate::leanh::lean_dec(v_head_622_);
                            if crate::leanh::lean_obj_tag(v___x_629_) == 0 {
                                let mut v___x_630_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                crate::leanh::lean_dec(v_val_628_);
                                crate::leanh::lean_dec(v_val_625_);
                                v___x_630_ = crate::leanh::lean_box(0);
                                return v___x_630_;
                            } else {
                                let mut v_val_631_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_632_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v_val_631_ = crate::leanh::lean_ctor_get(v___x_629_, 0);
                                crate::leanh::lean_inc(v_val_631_);
                                crate::leanh::lean_dec_ref_known(v___x_629_, 1);
                                v___x_632_ =
                                    l_Lake_Date_ofValid_x3f(v_val_625_, v_val_628_, v_val_631_);
                                return v___x_632_;
                            }
                        }
                    }
                } else {
                    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_tail_618_, 2);
                    crate::leanh::lean_dec_ref_known(v_tail_617_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_616_, 2);
                    v___x_633_ = crate::leanh::lean_box(0);
                    return v___x_633_;
                }
            } else {
                let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v_tail_617_, 2);
                crate::leanh::lean_dec(v_tail_618_);
                crate::leanh::lean_dec_ref_known(v___x_616_, 2);
                v___x_634_ = crate::leanh::lean_box(0);
                return v___x_634_;
            }
        } else {
            let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_tail_617_);
            crate::leanh::lean_dec_ref_known(v___x_616_, 2);
            v___x_635_ = crate::leanh::lean_box(0);
            return v___x_635_;
        }
    } else {
        let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_616_);
        v___x_636_ = crate::leanh::lean_box(0);
        return v___x_636_;
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(
    mut v_t_637_: *mut crate::leanh::LeanObject,
    mut v___x_638_: *mut crate::leanh::LeanObject,
    mut v___x_639_: *mut crate::leanh::LeanObject,
    mut v_inst_640_: *mut crate::leanh::LeanObject,
    mut v_R_641_: *mut crate::leanh::LeanObject,
    mut v_a_642_: *mut crate::leanh::LeanObject,
    mut v_b_643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_644_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(v_t_637_, v___x_638_, v___x_639_, v_a_642_, v_b_643_);
    return v___x_644_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___boxed(
    mut v_t_645_: *mut crate::leanh::LeanObject,
    mut v___x_646_: *mut crate::leanh::LeanObject,
    mut v___x_647_: *mut crate::leanh::LeanObject,
    mut v_inst_648_: *mut crate::leanh::LeanObject,
    mut v_R_649_: *mut crate::leanh::LeanObject,
    mut v_a_650_: *mut crate::leanh::LeanObject,
    mut v_b_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_652_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(v_t_645_, v___x_646_, v___x_647_, v_inst_648_, v_R_649_, v_a_650_, v_b_651_);
    crate::leanh::lean_dec_ref(v___x_646_);
    return v_res_652_;
}
pub unsafe fn l_Lake_Date_fromJson_x3f(
    mut v_j_656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_666_: u8 = 0;
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_j_656_) == 3 {
                    v_s_657_ = crate::leanh::lean_ctor_get(v_j_656_, 0);
                    crate::leanh::lean_inc_ref(v_s_657_);
                    crate::leanh::lean_dec_ref_known(v_j_656_, 1);
                    v___x_658_ = l_Lake_Date_ofString_x3f(v_s_657_);
                    if crate::leanh::lean_obj_tag(v___x_658_) == 1 {
                        v_val_659_ = crate::leanh::lean_ctor_get(v___x_658_, 0);
                        v_isSharedCheck_666_ = (!crate::leanh::lean_is_exclusive(v___x_658_)) as u8;
                        if v_isSharedCheck_666_ == 0 {
                            v___x_661_ = v___x_658_;
                            v_isShared_662_ = v_isSharedCheck_666_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_659_);
                            crate::leanh::lean_dec(v___x_658_);
                            v___x_661_ = crate::leanh::lean_box(0);
                            v_isShared_662_ = v_isSharedCheck_666_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_658_);
                        v___x_667_ = l_Lake_Date_fromJson_x3f___closed__1;
                        return v___x_667_;
                    }
                } else {
                    crate::leanh::lean_dec(v_j_656_);
                    v___x_668_ = l_Lake_Date_fromJson_x3f___closed__1;
                    return v___x_668_;
                }
            }
            1 => {
                if v_isShared_662_ == 0 {
                    v___x_664_ = v___x_661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_665_, 0, v_val_659_);
                    v___x_664_ = v_reuseFailAlloc_665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_664_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Date_toString(
    mut v_d_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_year_673_ = crate::leanh::lean_ctor_get(v_d_672_, 0);
    crate::leanh::lean_inc(v_year_673_);
    v_month_674_ = crate::leanh::lean_ctor_get(v_d_672_, 1);
    crate::leanh::lean_inc(v_month_674_);
    v_day_675_ = crate::leanh::lean_ctor_get(v_d_672_, 2);
    crate::leanh::lean_inc(v_day_675_);
    crate::leanh::lean_dec_ref(v_d_672_);
    v___x_676_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_677_ = l_Lake_zpad(v_year_673_, v___x_676_);
    v___x_678_ = l_Lake_Date_toString___closed__0;
    v___x_679_ = lean_string_append(v___x_677_, v___x_678_);
    v___x_680_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_681_ = l_Lake_zpad(v_month_674_, v___x_680_);
    v___x_682_ = lean_string_append(v___x_679_, v___x_681_);
    crate::leanh::lean_dec_ref(v___x_681_);
    v___x_683_ = lean_string_append(v___x_682_, v___x_678_);
    v___x_684_ = l_Lake_zpad(v_day_675_, v___x_680_);
    v___x_685_ = lean_string_append(v___x_683_, v___x_684_);
    crate::leanh::lean_dec_ref(v___x_684_);
    return v___x_685_;
}
pub unsafe fn l_Lake_Date_toJson(
    mut v_d_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Lake_Date_toString(v_d_688_);
    v___x_690_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_690_, 0, v___x_689_);
    return v___x_690_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Date(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_Date_instLT = _init_l_Lake_Date_instLT();
    crate::leanh::lean_mark_persistent(l_Lake_Date_instLT);
    l_Lake_Date_instLE = _init_l_Lake_Date_instLE();
    crate::leanh::lean_mark_persistent(l_Lake_Date_instLE);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Date(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Date(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Json(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Date(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Date(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Date(builtin);
}
