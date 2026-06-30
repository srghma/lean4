// Lean compiler output
// Module: Lean.Meta.TryThis
// Imports: Lean.Data.Lsp.Basic Lean.PrettyPrinter
use crate::ffi::{
    lean_float_add, lean_float_decLe, lean_float_mul, lean_float_sub, lean_float_to_string,
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_string_append, lean_string_utf8_byte_size,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_dec_eq, pow, round,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_pretty;
use crate::r#gen::Init::Data::OfScientific::{l_Float_ofScientific, lean_float_of_nat};
use crate::r#gen::Init::Data::String::Basic::{
    l_String_Slice_Pos_next_x21, l_String_Slice_pos_x21, l_String_slice_x21,
};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_mkObj;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    initialize_Lean_Data_Lsp_Basic, runtime_initialize_Lean_Data_Lsp_Basic,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_FileMap_utf8RangeToLspRange;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax};
use crate::r#gen::Lean::PrettyPrinter::{
    initialize_Lean_PrettyPrinter, l_Lean_PrettyPrinter_ppCategory,
    runtime_initialize_Lean_PrettyPrinter,
};
pub static l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value:
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
    m_data: [99, 108, 97, 115, 115, 78, 97, 109, 101, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1_value:
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
    m_data: [112, 111, 105, 110, 116, 101, 114, 32, 100, 105, 109, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4_value:
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
    m_data: [115, 116, 121, 108, 101, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5_value:
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
    m_data: [99, 111, 108, 111, 114, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        118, 97, 114, 40, 45, 45, 118, 115, 99, 111, 100, 101, 45, 101, 114, 114, 111, 114, 70,
        111, 114, 101, 103, 114, 111, 117, 110, 100, 41, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11_value:
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
        116, 101, 120, 116, 68, 101, 99, 111, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12_value:
    leanh::LeanStringObject<56> = leanh::LeanStringObject {
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
        117, 110, 100, 101, 114, 108, 105, 110, 101, 32, 119, 97, 118, 121, 32, 118, 97, 114, 40,
        45, 45, 118, 115, 99, 111, 100, 101, 45, 101, 100, 105, 116, 111, 114, 69, 114, 114, 111,
        114, 45, 102, 111, 114, 101, 103, 114, 111, 117, 110, 100, 41, 32, 49, 112, 116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13_value:
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
        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__0_value:
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
        103, 111, 108, 100, 32, 112, 111, 105, 110, 116, 101, 114, 32, 100, 105, 109, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1_value:
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
        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5_value:
    leanh::LeanStringObject<58> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        117, 110, 100, 101, 114, 108, 105, 110, 101, 32, 119, 97, 118, 121, 32, 118, 97, 114, 40,
        45, 45, 118, 115, 99, 111, 100, 101, 45, 101, 100, 105, 116, 111, 114, 87, 97, 114, 110,
        105, 110, 103, 45, 102, 111, 114, 101, 103, 114, 111, 117, 110, 100, 41, 32, 49, 112, 116,
        0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6_value:
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
        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__0_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
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
        105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 32, 112, 111, 105, 110, 116, 101,
        114, 32, 100, 105, 109, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1_value:
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
        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__0_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        103, 111, 97, 108, 45, 104, 121, 112, 32, 112, 111, 105, 110, 116, 101, 114, 32, 100, 105,
        109, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1_value:
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
        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__0_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        103, 111, 97, 108, 45, 105, 110, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 32, 112,
        111, 105, 110, 116, 101, 114, 32, 100, 105, 109, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1_value:
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
        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0_value:
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
    m_data: [104, 115, 108, 40, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1: f64 = 0.0;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2_value:
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
    m_data: [32, 57, 53, 37, 32, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3: f64 = 0.0;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4: f64 = 0.0;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5: f64 = 0.0;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6_value:
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
    m_data: [37, 41, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7_value:
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
    m_data: [116, 105, 116, 108, 101, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8_value:
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
        65, 112, 112, 108, 121, 32, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9_value:
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
        65, 112, 112, 108, 121, 32, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 32, 40, 0,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10_value:
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
    m_data: [41, 0],
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11: f64 = 0.0;
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12: f64 = 0.0;
pub static l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0_value:
    leanh::LeanCtorObject<6> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText_default___closed__0_value
        ) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion: *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion_default___closed__0_value
)
    as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [84, 114, 121, 84, 104, 105, 115, 0]};
static mut l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_TryThis_instImpl___closed__4_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 114, 121, 84, 104, 105, 115, 73, 110, 102, 111, 0]};
static mut l_Lean_Meta_Tactic_TryThis_instImpl___closed__4_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__4_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15353829308266697735 as *mut leanh::LeanObject] };
static l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject,8327623967363774415 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__4_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject,12327973545292099673 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__5_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 111, 114, 109, 97, 116, 0]};
static mut l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 112, 117, 116, 87, 105, 100, 116, 104, 0]};
static mut l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject,23689666010326313 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject,2377313009842426668 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 100, 101, 97, 108, 32, 105, 110, 112, 117, 116, 32, 119, 105, 100, 116, 104, 0]};
static mut l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 100 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__3_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__0_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__1_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__2_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject,15353829308266697735 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_TryThis_instImpl___closed__3_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12__value) as *mut leanh::LeanObject,8327623967363774415 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__0_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject,1400580424154811013 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__1_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject,3979875193395827984 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_TryThis_format_inputWidth: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx(
    mut v_x_654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_654_) == 0 {
        let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_655_ = leanh::lean_unsigned_to_nat(0);
        return v___x_655_;
    } else {
        let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_656_ = leanh::lean_unsigned_to_nat(1);
        return v___x_656_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx___boxed(
    mut v_x_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_658_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorIdx(v_x_657_);
    leanh::lean_dec_ref(v_x_657_);
    return v_res_658_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(
    mut v_t_659_: *mut leanh::LeanObject,
    mut v_k_660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_659_) == 0 {
        let mut v_kind_661_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_662_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_kind_661_ = leanh::lean_ctor_get(v_t_659_, 0);
        leanh::lean_inc(v_kind_661_);
        v_a_662_ = leanh::lean_ctor_get(v_t_659_, 1);
        leanh::lean_inc(v_a_662_);
        leanh::lean_dec_ref_known(v_t_659_, 2);
        v___x_663_ = leanh::lean_apply_2(v_k_660_, v_kind_661_, v_a_662_);
        return v___x_663_;
    } else {
        let mut v_a_664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_664_ = leanh::lean_ctor_get(v_t_659_, 0);
        leanh::lean_inc_ref(v_a_664_);
        leanh::lean_dec_ref_known(v_t_659_, 1);
        v___x_665_ = leanh::lean_apply_1(v_k_660_, v_a_664_);
        return v___x_665_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim(
    mut v_motive_666_: *mut leanh::LeanObject,
    mut v_ctorIdx_667_: *mut leanh::LeanObject,
    mut v_t_668_: *mut leanh::LeanObject,
    mut v_h_669_: *mut leanh::LeanObject,
    mut v_k_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_668_, v_k_670_);
    return v___x_671_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___boxed(
    mut v_motive_672_: *mut leanh::LeanObject,
    mut v_ctorIdx_673_: *mut leanh::LeanObject,
    mut v_t_674_: *mut leanh::LeanObject,
    mut v_h_675_: *mut leanh::LeanObject,
    mut v_k_676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim(
        v_motive_672_,
        v_ctorIdx_673_,
        v_t_674_,
        v_h_675_,
        v_k_676_,
    );
    leanh::lean_dec(v_ctorIdx_673_);
    return v_res_677_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_tsyntax_elim___redArg(
    mut v_t_678_: *mut leanh::LeanObject,
    mut v_tsyntax_679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ =
        l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_678_, v_tsyntax_679_);
    return v___x_680_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_tsyntax_elim(
    mut v_motive_681_: *mut leanh::LeanObject,
    mut v_t_682_: *mut leanh::LeanObject,
    mut v_h_683_: *mut leanh::LeanObject,
    mut v_tsyntax_684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_685_ =
        l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_682_, v_tsyntax_684_);
    return v___x_685_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_string_elim___redArg(
    mut v_t_686_: *mut leanh::LeanObject,
    mut v_string_687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_688_ =
        l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_686_, v_string_687_);
    return v___x_688_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_string_elim(
    mut v_motive_689_: *mut leanh::LeanObject,
    mut v_t_690_: *mut leanh::LeanObject,
    mut v_h_691_: *mut leanh::LeanObject,
    mut v_string_692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ =
        l_Lean_Meta_Tactic_TryThis_SuggestionText_ctorElim___redArg(v_t_690_, v_string_692_);
    return v___x_693_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText___lam__0(
    mut v_x_699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_705_: u8 = 0;
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_699_) == 0 {
                    v_a_700_ = leanh::lean_ctor_get(v_x_699_, 1);
                    leanh::lean_inc(v_a_700_);
                    leanh::lean_dec_ref_known(v_x_699_, 2);
                    v___x_701_ = l_Lean_MessageData_ofSyntax(v_a_700_);
                    return v___x_701_;
                } else {
                    v_a_702_ = leanh::lean_ctor_get(v_x_699_, 0);
                    v_isSharedCheck_710_ = (!leanh::lean_is_exclusive(v_x_699_)) as u8;
                    if v_isSharedCheck_710_ == 0 {
                        v___x_704_ = v_x_699_;
                        v_isShared_705_ = v_isSharedCheck_710_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_702_);
                        leanh::lean_dec(v_x_699_);
                        v___x_704_ = leanh::lean_box(0);
                        v_isShared_705_ = v_isSharedCheck_710_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_705_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_704_, 3);
                    v___x_707_ = v___x_704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_709_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_702_);
                    v___x_707_ = v_reuseFailAlloc_709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_708_ = l_Lean_MessageData_ofFormat(v___x_707_);
                return v___x_708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0(
    mut v_kind_713_: *mut leanh::LeanObject,
    mut v_a_714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_715_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_715_, 0, v_kind_713_);
    leanh::lean_ctor_set(v___x_715_, 1, v_a_714_);
    return v___x_715_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText(
    mut v_kind_716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_717_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_717_, 0, v_kind_716_);
    return v___f_717_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText___lam__0(
    mut v_a_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_719_, 0, v_a_718_);
    return v___x_719_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1()
-> *mut leanh::LeanObject {
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_722_ = leanh::lean_box(0);
    return v___x_722_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle()
-> *mut leanh::LeanObject {
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_723_ = leanh::lean_box(0);
    return v___x_723_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___aux__1(
    mut v_a_724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_724_);
    return v_a_724_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___aux__1___boxed(
    mut v_a_725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_726_ = l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___aux__1(v_a_725_);
    leanh::lean_dec(v_a_725_);
    return v_res_726_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0(
    mut v___y_727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___y_727_);
    return v___y_727_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0___boxed(
    mut v___y_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Lean_Meta_Tactic_TryThis_instToJsonSuggestionStyle___lam__0(v___y_728_);
    leanh::lean_dec(v___y_728_);
    return v_res_729_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_750_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9;
    v___x_751_ = l_Lean_Json_mkObj(v___x_750_);
    return v___x_751_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16;
    v___x_766_ = l_Lean_Json_mkObj(v___x_765_);
    return v___x_766_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(
    mut v_decorated_767_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_decorated_767_ == 0 {
                    v___x_777_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10_once
                        ),
                        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10,
                    );
                    v___y_769_ = v___x_777_;
                    state = 1;
                    continue;
                } else {
                    v___x_778_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17_once
                        ),
                        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17,
                    );
                    v___y_769_ = v___x_778_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_770_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3;
                v___x_771_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4;
                leanh::lean_inc(v___y_769_);
                v___x_772_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_772_, 0, v___x_771_);
                leanh::lean_ctor_set(v___x_772_, 1, v___y_769_);
                v___x_773_ = leanh::lean_box(0);
                v___x_774_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_774_, 0, v___x_772_);
                leanh::lean_ctor_set(v___x_774_, 1, v___x_773_);
                v___x_775_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_775_, 0, v___x_770_);
                leanh::lean_ctor_set(v___x_775_, 1, v___x_774_);
                v___x_776_ = l_Lean_Json_mkObj(v___x_775_);
                leanh::lean_dec_ref_known(v___x_775_, 2);
                return v___x_776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___boxed(
    mut v_decorated_779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decorated_boxed_780_: u8 = 0;
    let mut v_res_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decorated_boxed_780_ = (leanh::lean_unbox(v_decorated_779_) as u8);
    v_res_781_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(v_decorated_boxed_780_);
    return v_res_781_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_791_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3;
    v___x_792_ = l_Lean_Json_mkObj(v___x_791_);
    return v___x_792_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8;
    v___x_803_ = l_Lean_Json_mkObj(v___x_802_);
    return v___x_803_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9_once
        ),
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9,
    );
    v___x_805_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4;
    v___x_806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_806_, 0, v___x_805_);
    leanh::lean_ctor_set(v___x_806_, 1, v___x_804_);
    return v___x_806_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = leanh::lean_box(0);
    v___x_808_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10_once
        ),
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10,
    );
    v___x_809_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_809_, 0, v___x_808_);
    leanh::lean_ctor_set(v___x_809_, 1, v___x_807_);
    return v___x_809_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11_once
        ),
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11,
    );
    v___x_811_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2;
    v___x_812_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_812_, 0, v___x_811_);
    leanh::lean_ctor_set(v___x_812_, 1, v___x_810_);
    return v___x_812_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12_once
        ),
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12,
    );
    v___x_814_ = l_Lean_Json_mkObj(v___x_813_);
    return v___x_814_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(
    mut v_decorated_815_: u8,
) -> *mut leanh::LeanObject {
    if v_decorated_815_ == 0 {
        let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_816_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4_once
            ),
            _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4,
        );
        return v___x_816_;
    } else {
        let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_817_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13_once
            ),
            _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13,
        );
        return v___x_817_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___boxed(
    mut v_decorated_818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decorated_boxed_819_: u8 = 0;
    let mut v_res_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decorated_boxed_819_ = (leanh::lean_unbox(v_decorated_818_) as u8);
    v_res_820_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(v_decorated_boxed_819_);
    return v_res_820_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_830_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3;
    v___x_831_ = l_Lean_Json_mkObj(v___x_830_);
    return v___x_831_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success()
-> *mut leanh::LeanObject {
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4,
    );
    return v___x_832_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_842_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3;
    v___x_843_ = l_Lean_Json_mkObj(v___x_842_);
    return v___x_843_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis()
-> *mut leanh::LeanObject {
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4,
    );
    return v___x_844_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3;
    v___x_855_ = l_Lean_Json_mkObj(v___x_854_);
    return v___x_855_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible()
-> *mut leanh::LeanObject {
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_856_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4,
    );
    return v___x_856_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1() -> f64 {
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: f64 = 0.0;
    v___x_858_ = leanh::lean_unsigned_to_nat(120);
    v___x_859_ = lean_float_of_nat(v___x_858_);
    return v___x_859_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3() -> f64 {
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: f64 = 0.0;
    v___x_861_ = leanh::lean_unsigned_to_nat(60);
    v___x_862_ = lean_float_of_nat(v___x_861_);
    return v___x_862_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4() -> f64 {
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: f64 = 0.0;
    v___x_863_ = leanh::lean_unsigned_to_nat(2);
    v___x_864_ = lean_float_of_nat(v___x_863_);
    return v___x_864_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5() -> f64 {
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: u8 = 0;
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: f64 = 0.0;
    v___x_865_ = leanh::lean_unsigned_to_nat(2);
    v___x_866_ = 1;
    v___x_867_ = leanh::lean_unsigned_to_nat(75);
    v___x_868_ = l_Float_ofScientific(v___x_867_, v___x_866_, v___x_865_);
    return v___x_868_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11() -> f64 {
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: f64 = 0.0;
    v___x_874_ = leanh::lean_unsigned_to_nat(1);
    v___x_875_ = lean_float_of_nat(v___x_874_);
    return v___x_875_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12() -> f64 {
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: f64 = 0.0;
    v___x_876_ = leanh::lean_unsigned_to_nat(0);
    v___x_877_ = lean_float_of_nat(v___x_876_);
    return v___x_877_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(
    mut v_t_878_: f64,
    mut v_showValueInHoverText_879_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_894_: f64 = 0.0;
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: f64 = 0.0;
    let mut v___x_900_: f64 = 0.0;
    let mut v___x_901_: f64 = 0.0;
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: f64 = 0.0;
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: u8 = 0;
    let mut v___x_909_: f64 = 0.0;
    let mut v___x_910_: f64 = 0.0;
    let mut v___x_911_: f64 = 0.0;
    let mut v___x_912_: f64 = 0.0;
    let mut v___x_913_: f64 = 0.0;
    let mut v___x_914_: f64 = 0.0;
    let mut v___x_915_: f64 = 0.0;
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_934_: f64 = 0.0;
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: f64 = 0.0;
    let mut v___x_937_: u8 = 0;
    let mut v___x_938_: f64 = 0.0;
    let mut v___x_939_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_938_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12,
                );
                v___x_939_ = lean_float_decLe(v_t_878_, v___x_938_);
                if v___x_939_ == 0 {
                    v___y_934_ = v_t_878_;
                    state = 3;
                    continue;
                } else {
                    v___y_934_ = v___x_938_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_886_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_886_, 0, v___y_885_);
                leanh::lean_inc_ref(v___y_883_);
                v___x_887_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_887_, 0, v___y_883_);
                leanh::lean_ctor_set(v___x_887_, 1, v___x_886_);
                leanh::lean_inc(v___y_884_);
                v___x_888_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_888_, 0, v___x_887_);
                leanh::lean_ctor_set(v___x_888_, 1, v___y_884_);
                v___x_889_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_889_, 0, v___y_882_);
                leanh::lean_ctor_set(v___x_889_, 1, v___x_888_);
                leanh::lean_inc_ref(v___y_881_);
                v___x_890_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_890_, 0, v___y_881_);
                leanh::lean_ctor_set(v___x_890_, 1, v___x_889_);
                v___x_891_ = l_Lean_Json_mkObj(v___x_890_);
                leanh::lean_dec_ref_known(v___x_890_, 2);
                return v___x_891_;
            }
            2 => {
                v___x_895_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3;
                v___x_896_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4;
                v___x_897_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5;
                v___x_898_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__0;
                v___x_899_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1,
                );
                v___x_900_ = lean_float_mul(v___y_894_, v___x_899_);
                v___x_901_ = round(v___x_900_);
                v___x_902_ = lean_float_to_string(v___x_901_);
                v___x_903_ = lean_string_append(v___x_898_, v___x_902_);
                leanh::lean_dec_ref(v___x_902_);
                v___x_904_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2;
                v___x_905_ = lean_string_append(v___x_903_, v___x_904_);
                v___x_906_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3,
                );
                v___x_907_ = leanh::lean_unsigned_to_nat(5);
                v___x_908_ = 1;
                v___x_909_ = l_Float_ofScientific(v___x_907_, v___x_908_, v___y_893_);
                v___x_910_ = lean_float_sub(v___y_894_, v___x_909_);
                v___x_911_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4,
                );
                v___x_912_ = pow(v___x_910_, v___x_911_);
                v___x_913_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5,
                );
                v___x_914_ = lean_float_add(v___x_912_, v___x_913_);
                v___x_915_ = lean_float_mul(v___x_906_, v___x_914_);
                v___x_916_ = lean_float_to_string(v___x_915_);
                v___x_917_ = lean_string_append(v___x_905_, v___x_916_);
                leanh::lean_dec_ref(v___x_916_);
                v___x_918_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6;
                v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
                v___x_920_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_920_, 0, v___x_919_);
                v___x_921_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_921_, 0, v___x_897_);
                leanh::lean_ctor_set(v___x_921_, 1, v___x_920_);
                v___x_922_ = leanh::lean_box(0);
                v___x_923_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_923_, 0, v___x_921_);
                leanh::lean_ctor_set(v___x_923_, 1, v___x_922_);
                v___x_924_ = l_Lean_Json_mkObj(v___x_923_);
                leanh::lean_dec_ref_known(v___x_923_, 2);
                v___x_925_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_925_, 0, v___x_896_);
                leanh::lean_ctor_set(v___x_925_, 1, v___x_924_);
                v___x_926_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7;
                if v_showValueInHoverText_879_ == 0 {
                    v___x_927_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8;
                    v___y_881_ = v___x_895_;
                    v___y_882_ = v___x_925_;
                    v___y_883_ = v___x_926_;
                    v___y_884_ = v___x_922_;
                    v___y_885_ = v___x_927_;
                    state = 1;
                    continue;
                } else {
                    v___x_928_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9;
                    v___x_929_ = lean_float_to_string(v___y_894_);
                    v___x_930_ = lean_string_append(v___x_928_, v___x_929_);
                    leanh::lean_dec_ref(v___x_929_);
                    v___x_931_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10;
                    v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
                    v___y_881_ = v___x_895_;
                    v___y_882_ = v___x_925_;
                    v___y_883_ = v___x_926_;
                    v___y_884_ = v___x_922_;
                    v___y_885_ = v___x_932_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_935_ = leanh::lean_unsigned_to_nat(1);
                v___x_936_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11_once
                    ),
                    _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11,
                );
                v___x_937_ = lean_float_decLe(v___y_934_, v___x_936_);
                if v___x_937_ == 0 {
                    v___y_893_ = v___x_935_;
                    v___y_894_ = v___x_936_;
                    state = 2;
                    continue;
                } else {
                    v___y_893_ = v___x_935_;
                    v___y_894_ = v___y_934_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___boxed(
    mut v_t_940_: *mut leanh::LeanObject,
    mut v_showValueInHoverText_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_942_: f64 = 0.0;
    let mut v_showValueInHoverText_boxed_943_: u8 = 0;
    let mut v_res_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_942_ = leanh::lean_unbox_float(v_t_940_);
    leanh::lean_dec_ref(v_t_940_);
    v_showValueInHoverText_boxed_943_ =
        (leanh::lean_unbox(v_showValueInHoverText_941_) as u8);
    v_res_944_ = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(
        v_t_boxed_942_,
        v_showValueInHoverText_boxed_943_,
    );
    return v_res_944_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion___lam__0(
    mut v_s_950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_messageData_x3f_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suggestion_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_958_: u8 = 0;
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_963_: u8 = 0;
    let mut v_val_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_messageData_x3f_951_ = leanh::lean_ctor_get(v_s_950_, 4);
                if leanh::lean_obj_tag(v_messageData_x3f_951_) == 0 {
                    v_suggestion_952_ = leanh::lean_ctor_get(v_s_950_, 0);
                    leanh::lean_inc_ref(v_suggestion_952_);
                    leanh::lean_dec_ref(v_s_950_);
                    if leanh::lean_obj_tag(v_suggestion_952_) == 0 {
                        v_a_953_ = leanh::lean_ctor_get(v_suggestion_952_, 1);
                        leanh::lean_inc(v_a_953_);
                        leanh::lean_dec_ref_known(v_suggestion_952_, 2);
                        v___x_954_ = l_Lean_MessageData_ofSyntax(v_a_953_);
                        return v___x_954_;
                    } else {
                        v_a_955_ = leanh::lean_ctor_get(v_suggestion_952_, 0);
                        v_isSharedCheck_963_ =
                            (!leanh::lean_is_exclusive(v_suggestion_952_)) as u8;
                        if v_isSharedCheck_963_ == 0 {
                            v___x_957_ = v_suggestion_952_;
                            v_isShared_958_ = v_isSharedCheck_963_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_955_);
                            leanh::lean_dec(v_suggestion_952_);
                            v___x_957_ = leanh::lean_box(0);
                            v_isShared_958_ = v_isSharedCheck_963_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc_ref(v_messageData_x3f_951_);
                    leanh::lean_dec_ref(v_s_950_);
                    v_val_964_ = leanh::lean_ctor_get(v_messageData_x3f_951_, 0);
                    leanh::lean_inc(v_val_964_);
                    leanh::lean_dec_ref_known(v_messageData_x3f_951_, 1);
                    return v_val_964_;
                }
            }
            1 => {
                if v_isShared_958_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_957_, 3);
                    v___x_960_ = v___x_957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_962_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_955_);
                    v___x_960_ = v_reuseFailAlloc_962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_961_ = l_Lean_MessageData_ofFormat(v___x_960_);
                return v___x_961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion___lam__0(
    mut v_t_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_968_ = leanh::lean_box(0);
    v___x_969_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_969_, 0, v_t_967_);
    leanh::lean_ctor_set(v___x_969_, 1, v___x_968_);
    leanh::lean_ctor_set(v___x_969_, 2, v___x_968_);
    leanh::lean_ctor_set(v___x_969_, 3, v___x_968_);
    leanh::lean_ctor_set(v___x_969_, 4, v___x_968_);
    leanh::lean_ctor_set(v___x_969_, 5, v___x_968_);
    return v___x_969_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(
    mut v_s_985_: *mut leanh::LeanObject,
    mut v_a_986_: *mut leanh::LeanObject,
    mut v_b_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u8 = 0;
    let mut v_str_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: u32 = 0;
    let mut v___x_1000_: u32 = 0;
    let mut v___x_1001_: u8 = 0;
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_988_ = leanh::lean_unsigned_to_nat(0);
                v___x_989_ = lean_nat_dec_eq(v_a_986_, v___x_988_);
                if v___x_989_ == 0 {
                    v_str_990_ = leanh::lean_ctor_get(v_s_985_, 0);
                    v_startInclusive_991_ = leanh::lean_ctor_get(v_s_985_, 1);
                    v___x_992_ = lean_nat_add(v_startInclusive_991_, v_a_986_);
                    leanh::lean_inc(v___x_992_);
                    leanh::lean_inc(v_startInclusive_991_);
                    leanh::lean_inc_ref(v_str_990_);
                    v___x_993_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_993_, 0, v_str_990_);
                    leanh::lean_ctor_set(v___x_993_, 1, v_startInclusive_991_);
                    leanh::lean_ctor_set(v___x_993_, 2, v___x_992_);
                    v___x_994_ = lean_nat_sub(v___x_992_, v_startInclusive_991_);
                    leanh::lean_dec(v___x_992_);
                    v___x_995_ = leanh::lean_unsigned_to_nat(1);
                    v___x_996_ = lean_nat_sub(v___x_994_, v___x_995_);
                    leanh::lean_dec(v___x_994_);
                    v___x_997_ = l_String_Slice_posLE(v___x_993_, v___x_996_);
                    leanh::lean_dec_ref_known(v___x_993_, 3);
                    v___x_998_ = lean_nat_add(v_startInclusive_991_, v___x_997_);
                    v___x_999_ = lean_string_utf8_get_fast(v_str_990_, v___x_998_);
                    leanh::lean_dec(v___x_998_);
                    v___x_1000_ = 10;
                    v___x_1001_ = lean_uint32_dec_eq(v___x_999_, v___x_1000_);
                    if v___x_1001_ == 0 {
                        leanh::lean_dec(v___x_997_);
                        v___x_1002_ = leanh::lean_box(0);
                        v___x_1003_ = lean_nat_sub(v_a_986_, v___x_995_);
                        leanh::lean_dec(v_a_986_);
                        v___x_1004_ = l_String_Slice_posLE(v_s_985_, v___x_1003_);
                        v_a_986_ = v___x_1004_;
                        v_b_987_ = v___x_1002_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_986_);
                        v___x_1006_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1006_, 0, v___x_997_);
                        return v___x_1006_;
                    }
                } else {
                    leanh::lean_dec(v_a_986_);
                    leanh::lean_inc(v_b_987_);
                    return v_b_987_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg___boxed(
    mut v_s_1007_: *mut leanh::LeanObject,
    mut v_a_1008_: *mut leanh::LeanObject,
    mut v_b_1009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_1007_, v_a_1008_, v_b_1009_);
    leanh::lean_dec(v_b_1009_);
    leanh::lean_dec_ref(v_s_1007_);
    return v_res_1010_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(
    mut v_s_1011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_1012_ = leanh::lean_ctor_get(v_s_1011_, 1);
    v_endExclusive_1013_ = leanh::lean_ctor_get(v_s_1011_, 2);
    v_searcher_1014_ = lean_nat_sub(v_endExclusive_1013_, v_startInclusive_1012_);
    v___x_1015_ = leanh::lean_box(0);
    v___x_1016_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_1011_, v_searcher_1014_, v___x_1015_);
    return v___x_1016_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0___boxed(
    mut v_s_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(v_s_1017_);
    leanh::lean_dec_ref(v_s_1017_);
    return v_res_1018_;
}
pub unsafe fn l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart(
    mut v_s_1019_: *mut leanh::LeanObject,
    mut v_p_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1027_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_s_1019_);
                v___x_1028_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1028_, 0, v_s_1019_);
                leanh::lean_ctor_set(v___x_1028_, 1, v___x_1027_);
                leanh::lean_ctor_set(v___x_1028_, 2, v_p_1020_);
                v___x_1029_ = l_String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0(v___x_1028_);
                leanh::lean_dec_ref_known(v___x_1028_, 3);
                if leanh::lean_obj_tag(v___x_1029_) == 0 {
                    if leanh::lean_obj_tag(v___x_1029_) == 0 {
                        leanh::lean_dec_ref(v_s_1019_);
                        return v___x_1027_;
                    } else {
                        v_val_1030_ = leanh::lean_ctor_get(v___x_1029_, 0);
                        leanh::lean_inc(v_val_1030_);
                        leanh::lean_dec_ref_known(v___x_1029_, 1);
                        v_val_1022_ = v_val_1030_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_val_1031_ = leanh::lean_ctor_get(v___x_1029_, 0);
                    leanh::lean_inc(v_val_1031_);
                    leanh::lean_dec_ref_known(v___x_1029_, 1);
                    v_val_1022_ = v_val_1031_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1023_ = leanh::lean_unsigned_to_nat(0);
                v___x_1024_ = lean_string_utf8_byte_size(v_s_1019_);
                v___x_1025_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1025_, 0, v_s_1019_);
                leanh::lean_ctor_set(v___x_1025_, 1, v___x_1023_);
                leanh::lean_ctor_set(v___x_1025_, 2, v___x_1024_);
                v___x_1026_ = l_String_Slice_Pos_next_x21(v___x_1025_, v_val_1022_);
                leanh::lean_dec(v_val_1022_);
                leanh::lean_dec_ref_known(v___x_1025_, 3);
                return v___x_1026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0(
    mut v_s_1032_: *mut leanh::LeanObject,
    mut v_inst_1033_: *mut leanh::LeanObject,
    mut v_R_1034_: *mut leanh::LeanObject,
    mut v_a_1035_: *mut leanh::LeanObject,
    mut v_b_1036_: *mut leanh::LeanObject,
    mut v_c_1037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1038_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___redArg(v_s_1032_, v_a_1035_, v_b_1036_);
    return v___x_1038_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0___boxed(
    mut v_s_1039_: *mut leanh::LeanObject,
    mut v_inst_1040_: *mut leanh::LeanObject,
    mut v_R_1041_: *mut leanh::LeanObject,
    mut v_a_1042_: *mut leanh::LeanObject,
    mut v_b_1043_: *mut leanh::LeanObject,
    mut v_c_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart_spec__0_spec__0(v_s_1039_, v_inst_1040_, v_R_1041_, v_a_1042_, v_b_1043_, v_c_1044_);
    leanh::lean_dec(v_b_1043_);
    leanh::lean_dec_ref(v_s_1039_);
    return v_res_1045_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(
    mut v___x_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
    mut v_b_1048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: u32 = 0;
    let mut v___x_1056_: u32 = 0;
    let mut v___x_1057_: u8 = 0;
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1049_ = leanh::lean_ctor_get(v___x_1046_, 0);
                v_startInclusive_1050_ = leanh::lean_ctor_get(v___x_1046_, 1);
                v_endExclusive_1051_ = leanh::lean_ctor_get(v___x_1046_, 2);
                v___x_1052_ = lean_nat_sub(v_endExclusive_1051_, v_startInclusive_1050_);
                v___x_1053_ = lean_nat_dec_eq(v_a_1047_, v___x_1052_);
                leanh::lean_dec(v___x_1052_);
                if v___x_1053_ == 0 {
                    v___x_1054_ = lean_nat_add(v_startInclusive_1050_, v_a_1047_);
                    v___x_1055_ = lean_string_utf8_get_fast(v_str_1049_, v___x_1054_);
                    v___x_1056_ = 32;
                    v___x_1057_ = lean_uint32_dec_eq(v___x_1055_, v___x_1056_);
                    if v___x_1057_ == 0 {
                        leanh::lean_dec(v___x_1054_);
                        v___x_1058_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1058_, 0, v_a_1047_);
                        return v___x_1058_;
                    } else {
                        if v___x_1053_ == 0 {
                            leanh::lean_dec(v_a_1047_);
                            v___x_1059_ = leanh::lean_box(0);
                            v___x_1060_ = lean_string_utf8_next_fast(v_str_1049_, v___x_1054_);
                            leanh::lean_dec(v___x_1054_);
                            v___x_1061_ = lean_nat_sub(v___x_1060_, v_startInclusive_1050_);
                            v_a_1047_ = v___x_1061_;
                            v_b_1048_ = v___x_1059_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1054_);
                            v___x_1063_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1063_, 0, v_a_1047_);
                            return v___x_1063_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1047_);
                    leanh::lean_inc(v_b_1048_);
                    return v_b_1048_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg___boxed(
    mut v___x_1064_: *mut leanh::LeanObject,
    mut v_a_1065_: *mut leanh::LeanObject,
    mut v_b_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1067_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_1064_, v_a_1065_, v_b_1066_);
    leanh::lean_dec(v_b_1066_);
    leanh::lean_dec_ref(v___x_1064_);
    return v_res_1067_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(
    mut v_map_1068_: *mut leanh::LeanObject,
    mut v_range_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_source_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v_searcher_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rangeStart_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1096_: u8 = 0;
    let mut v_unused_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_source_1070_ = leanh::lean_ctor_get(v_map_1068_, 0);
                leanh::lean_inc_ref(v_source_1070_);
                leanh::lean_dec_ref(v_map_1068_);
                v_start_1071_ = leanh::lean_ctor_get(v_range_1069_, 0);
                v_isSharedCheck_1096_ = (!leanh::lean_is_exclusive(v_range_1069_)) as u8;
                if v_isSharedCheck_1096_ == 0 {
                    v_unused_1097_ = leanh::lean_ctor_get(v_range_1069_, 1);
                    leanh::lean_dec(v_unused_1097_);
                    v___x_1073_ = v_range_1069_;
                    v_isShared_1074_ = v_isSharedCheck_1096_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_start_1071_);
                    leanh::lean_dec(v_range_1069_);
                    v___x_1073_ = leanh::lean_box(0);
                    v_isShared_1074_ = v_isSharedCheck_1096_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_searcher_1075_ = leanh::lean_unsigned_to_nat(0);
                v___x_1076_ = lean_string_utf8_byte_size(v_source_1070_);
                leanh::lean_inc_ref_n(v_source_1070_, 2);
                v___x_1077_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1077_, 0, v_source_1070_);
                leanh::lean_ctor_set(v___x_1077_, 1, v_searcher_1075_);
                leanh::lean_ctor_set(v___x_1077_, 2, v___x_1076_);
                v_rangeStart_1078_ = l_String_Slice_pos_x21(v___x_1077_, v_start_1071_);
                leanh::lean_dec_ref_known(v___x_1077_, 3);
                leanh::lean_inc(v_rangeStart_1078_);
                v_start_1079_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_getIndentAndColumn_findLineStart(v_source_1070_, v_rangeStart_1078_);
                v___x_1080_ = l_String_slice_x21(v_source_1070_, v_start_1079_, v_rangeStart_1078_);
                leanh::lean_dec(v_rangeStart_1078_);
                v___x_1090_ = leanh::lean_box(0);
                v___x_1091_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_1080_, v_searcher_1075_, v___x_1090_);
                if leanh::lean_obj_tag(v___x_1091_) == 0 {
                    v_startInclusive_1092_ = leanh::lean_ctor_get(v___x_1080_, 1);
                    leanh::lean_inc(v_startInclusive_1092_);
                    v_endExclusive_1093_ = leanh::lean_ctor_get(v___x_1080_, 2);
                    leanh::lean_inc(v_endExclusive_1093_);
                    v___x_1094_ = lean_nat_sub(v_endExclusive_1093_, v_startInclusive_1092_);
                    leanh::lean_dec(v_startInclusive_1092_);
                    leanh::lean_dec(v_endExclusive_1093_);
                    v___y_1082_ = v___x_1094_;
                    state = 2;
                    continue;
                } else {
                    v_val_1095_ = leanh::lean_ctor_get(v___x_1091_, 0);
                    leanh::lean_inc(v_val_1095_);
                    leanh::lean_dec_ref_known(v___x_1091_, 1);
                    v___y_1082_ = v_val_1095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_startInclusive_1083_ = leanh::lean_ctor_get(v___x_1080_, 1);
                leanh::lean_inc(v_startInclusive_1083_);
                leanh::lean_dec_ref(v___x_1080_);
                v___x_1084_ = lean_nat_add(v_startInclusive_1083_, v___y_1082_);
                leanh::lean_dec(v___y_1082_);
                leanh::lean_dec(v_startInclusive_1083_);
                v___x_1085_ = lean_nat_sub(v___x_1084_, v_start_1079_);
                leanh::lean_dec(v___x_1084_);
                v___x_1086_ = lean_nat_sub(v_start_1071_, v_start_1079_);
                leanh::lean_dec(v_start_1079_);
                leanh::lean_dec(v_start_1071_);
                if v_isShared_1074_ == 0 {
                    leanh::lean_ctor_set(v___x_1073_, 1, v___x_1086_);
                    leanh::lean_ctor_set(v___x_1073_, 0, v___x_1085_);
                    v___x_1088_ = v___x_1073_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1089_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1086_);
                    v___x_1088_ = v_reuseFailAlloc_1089_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0(
    mut v___x_1098_: *mut leanh::LeanObject,
    mut v_inst_1099_: *mut leanh::LeanObject,
    mut v_R_1100_: *mut leanh::LeanObject,
    mut v_a_1101_: *mut leanh::LeanObject,
    mut v_b_1102_: *mut leanh::LeanObject,
    mut v_c_1103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___redArg(v___x_1098_, v_a_1101_, v_b_1102_);
    return v___x_1104_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0___boxed(
    mut v___x_1105_: *mut leanh::LeanObject,
    mut v_inst_1106_: *mut leanh::LeanObject,
    mut v_R_1107_: *mut leanh::LeanObject,
    mut v_a_1108_: *mut leanh::LeanObject,
    mut v_b_1109_: *mut leanh::LeanObject,
    mut v_c_1110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1111_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_TryThis_getIndentAndColumn_spec__0(
            v___x_1105_,
            v_inst_1106_,
            v_R_1107_,
            v_a_1108_,
            v_b_1109_,
            v_c_1110_,
        );
    leanh::lean_dec(v_b_1109_);
    leanh::lean_dec_ref(v___x_1105_);
    return v_res_1111_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(
    mut v_name_1112_: *mut leanh::LeanObject,
    mut v_decl_1113_: *mut leanh::LeanObject,
    mut v_ref_1114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1124_: u8 = 0;
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1129_: u8 = 0;
    let mut v_unused_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1116_ = leanh::lean_ctor_get(v_decl_1113_, 0);
                v_descr_1117_ = leanh::lean_ctor_get(v_decl_1113_, 1);
                v_deprecation_x3f_1118_ = leanh::lean_ctor_get(v_decl_1113_, 2);
                leanh::lean_inc(v_defValue_1116_);
                v___x_1119_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1119_, 0, v_defValue_1116_);
                leanh::lean_inc(v_deprecation_x3f_1118_);
                leanh::lean_inc_ref(v_descr_1117_);
                leanh::lean_inc_n(v_name_1112_, 2);
                v___x_1120_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_1120_, 0, v_name_1112_);
                leanh::lean_ctor_set(v___x_1120_, 1, v_ref_1114_);
                leanh::lean_ctor_set(v___x_1120_, 2, v___x_1119_);
                leanh::lean_ctor_set(v___x_1120_, 3, v_descr_1117_);
                leanh::lean_ctor_set(v___x_1120_, 4, v_deprecation_x3f_1118_);
                v___x_1121_ = lean_register_option(v_name_1112_, v___x_1120_);
                if leanh::lean_obj_tag(v___x_1121_) == 0 {
                    v_isSharedCheck_1129_ = (!leanh::lean_is_exclusive(v___x_1121_)) as u8;
                    if v_isSharedCheck_1129_ == 0 {
                        v_unused_1130_ = leanh::lean_ctor_get(v___x_1121_, 0);
                        leanh::lean_dec(v_unused_1130_);
                        v___x_1123_ = v___x_1121_;
                        v_isShared_1124_ = v_isSharedCheck_1129_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1121_);
                        v___x_1123_ = leanh::lean_box(0);
                        v_isShared_1124_ = v_isSharedCheck_1129_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_1112_);
                    v_a_1131_ = leanh::lean_ctor_get(v___x_1121_, 0);
                    v_isSharedCheck_1138_ = (!leanh::lean_is_exclusive(v___x_1121_)) as u8;
                    if v_isSharedCheck_1138_ == 0 {
                        v___x_1133_ = v___x_1121_;
                        v_isShared_1134_ = v_isSharedCheck_1138_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1131_);
                        leanh::lean_dec(v___x_1121_);
                        v___x_1133_ = leanh::lean_box(0);
                        v_isShared_1134_ = v_isSharedCheck_1138_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_1116_);
                v___x_1125_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1125_, 0, v_name_1112_);
                leanh::lean_ctor_set(v___x_1125_, 1, v_defValue_1116_);
                if v_isShared_1124_ == 0 {
                    leanh::lean_ctor_set(v___x_1123_, 0, v___x_1125_);
                    v___x_1127_ = v___x_1123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1128_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
                    v___x_1127_ = v_reuseFailAlloc_1128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1127_;
            }
            3 => {
                if v_isShared_1134_ == 0 {
                    v___x_1136_ = v___x_1133_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1137_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
                    v___x_1136_ = v_reuseFailAlloc_1137_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1139_: *mut leanh::LeanObject,
    mut v_decl_1140_: *mut leanh::LeanObject,
    mut v_ref_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1143_ = l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(v_name_1139_, v_decl_1140_, v_ref_1141_);
    leanh::lean_dec_ref(v_decl_1140_);
    return v_res_1143_;
}
pub unsafe fn l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1162_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__2_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_;
    v___x_1163_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__4_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_;
    v___x_1164_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn___closed__5_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_;
    v___x_1165_ = l_Lean_Option_register___at___00__private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4__spec__0(v___x_1162_, v___x_1163_, v___x_1164_);
    return v___x_1165_;
}
pub unsafe fn l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4____boxed(
    mut v_a_1166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1167_ = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
    return v_res_1167_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(
    mut v_opts_1168_: *mut leanh::LeanObject,
    mut v_opt_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1170_ = leanh::lean_ctor_get(v_opt_1169_, 0);
    v_defValue_1171_ = leanh::lean_ctor_get(v_opt_1169_, 1);
    v_map_1172_ = leanh::lean_ctor_get(v_opts_1168_, 0);
    v___x_1173_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1172_,
            v_name_1170_,
        );
    if leanh::lean_obj_tag(v___x_1173_) == 0 {
        leanh::lean_inc(v_defValue_1171_);
        return v_defValue_1171_;
    } else {
        let mut v_val_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1174_ = leanh::lean_ctor_get(v___x_1173_, 0);
        leanh::lean_inc(v_val_1174_);
        leanh::lean_dec_ref_known(v___x_1173_, 1);
        if leanh::lean_obj_tag(v_val_1174_) == 3 {
            let mut v_v_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1175_ = leanh::lean_ctor_get(v_val_1174_, 0);
            leanh::lean_inc(v_v_1175_);
            leanh::lean_dec_ref_known(v_val_1174_, 1);
            return v_v_1175_;
        } else {
            leanh::lean_dec(v_val_1174_);
            leanh::lean_inc(v_defValue_1171_);
            return v_defValue_1171_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0___boxed(
    mut v_opts_1176_: *mut leanh::LeanObject,
    mut v_opt_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1178_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(
        v_opts_1176_,
        v_opt_1177_,
    );
    leanh::lean_dec_ref(v_opt_1177_);
    leanh::lean_dec_ref(v_opts_1176_);
    return v_res_1178_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_getInputWidth(
    mut v_o_1179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1180_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
    v___x_1181_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_TryThis_getInputWidth_spec__0(
        v_o_1179_,
        v___x_1180_,
    );
    return v___x_1181_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_getInputWidth___boxed(
    mut v_o_1182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1183_ = l_Lean_Meta_Tactic_TryThis_getInputWidth(v_o_1182_);
    leanh::lean_dec_ref(v_o_1182_);
    return v_res_1183_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(
    mut v_x_1184_: *mut leanh::LeanObject,
    mut v_a_1185_: *mut leanh::LeanObject,
    mut v_a_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1194_: u8 = 0;
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1184_) == 0 {
                    v_kind_1188_ = leanh::lean_ctor_get(v_x_1184_, 0);
                    leanh::lean_inc(v_kind_1188_);
                    v_a_1189_ = leanh::lean_ctor_get(v_x_1184_, 1);
                    leanh::lean_inc(v_a_1189_);
                    leanh::lean_dec_ref_known(v_x_1184_, 2);
                    v___x_1190_ = l_Lean_PrettyPrinter_ppCategory(
                        v_kind_1188_,
                        v_a_1189_,
                        v_a_1185_,
                        v_a_1186_,
                    );
                    return v___x_1190_;
                } else {
                    v_a_1191_ = leanh::lean_ctor_get(v_x_1184_, 0);
                    v_isSharedCheck_1199_ = (!leanh::lean_is_exclusive(v_x_1184_)) as u8;
                    if v_isSharedCheck_1199_ == 0 {
                        v___x_1193_ = v_x_1184_;
                        v_isShared_1194_ = v_isSharedCheck_1199_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1191_);
                        leanh::lean_dec(v_x_1184_);
                        v___x_1193_ = leanh::lean_box(0);
                        v_isShared_1194_ = v_isSharedCheck_1199_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1194_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1193_, 3);
                    v___x_1196_ = v___x_1193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1198_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1191_);
                    v___x_1196_ = v_reuseFailAlloc_1198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1197_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1197_, 0, v___x_1196_);
                return v___x_1197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty___boxed(
    mut v_x_1200_: *mut leanh::LeanObject,
    mut v_a_1201_: *mut leanh::LeanObject,
    mut v_a_1202_: *mut leanh::LeanObject,
    mut v_a_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1204_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(v_x_1200_, v_a_1201_, v_a_1202_);
    leanh::lean_dec(v_a_1202_);
    leanh::lean_dec_ref(v_a_1201_);
    return v_res_1204_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(
    mut v_s_1205_: *mut leanh::LeanObject,
    mut v_w_1206_: *mut leanh::LeanObject,
    mut v_indent_1207_: *mut leanh::LeanObject,
    mut v_column_1208_: *mut leanh::LeanObject,
    mut v_a_1209_: *mut leanh::LeanObject,
    mut v_a_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1227_: u8 = 0;
    let mut v_a_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut v_options_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1242_: u8 = 0;
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_s_1205_) == 0 {
                    v_kind_1212_ = leanh::lean_ctor_get(v_s_1205_, 0);
                    leanh::lean_inc(v_kind_1212_);
                    v_a_1213_ = leanh::lean_ctor_get(v_s_1205_, 1);
                    leanh::lean_inc(v_a_1213_);
                    leanh::lean_dec_ref_known(v_s_1205_, 2);
                    if leanh::lean_obj_tag(v_w_1206_) == 0 {
                        v_options_1236_ = leanh::lean_ctor_get(v_a_1209_, 2);
                        v___x_1237_ = l_Lean_Meta_Tactic_TryThis_getInputWidth(v_options_1236_);
                        v_w_1215_ = v___x_1237_;
                        v___y_1216_ = v_a_1209_;
                        v___y_1217_ = v_a_1210_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1238_ = leanh::lean_ctor_get(v_w_1206_, 0);
                        leanh::lean_inc(v_val_1238_);
                        leanh::lean_dec_ref_known(v_w_1206_, 1);
                        v_w_1215_ = v_val_1238_;
                        v___y_1216_ = v_a_1209_;
                        v___y_1217_ = v_a_1210_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_column_1208_);
                    leanh::lean_dec(v_indent_1207_);
                    leanh::lean_dec(v_w_1206_);
                    v_a_1239_ = leanh::lean_ctor_get(v_s_1205_, 0);
                    v_isSharedCheck_1246_ = (!leanh::lean_is_exclusive(v_s_1205_)) as u8;
                    if v_isSharedCheck_1246_ == 0 {
                        v___x_1241_ = v_s_1205_;
                        v_isShared_1242_ = v_isSharedCheck_1246_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1239_);
                        leanh::lean_dec(v_s_1205_);
                        v___x_1241_ = leanh::lean_box(0);
                        v_isShared_1242_ = v_isSharedCheck_1246_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1218_ = l_Lean_PrettyPrinter_ppCategory(
                    v_kind_1212_,
                    v_a_1213_,
                    v___y_1216_,
                    v___y_1217_,
                );
                if leanh::lean_obj_tag(v___x_1218_) == 0 {
                    v_a_1219_ = leanh::lean_ctor_get(v___x_1218_, 0);
                    v_isSharedCheck_1227_ = (!leanh::lean_is_exclusive(v___x_1218_)) as u8;
                    if v_isSharedCheck_1227_ == 0 {
                        v___x_1221_ = v___x_1218_;
                        v_isShared_1222_ = v_isSharedCheck_1227_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1219_);
                        leanh::lean_dec(v___x_1218_);
                        v___x_1221_ = leanh::lean_box(0);
                        v_isShared_1222_ = v_isSharedCheck_1227_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_w_1215_);
                    leanh::lean_dec(v_column_1208_);
                    leanh::lean_dec(v_indent_1207_);
                    v_a_1228_ = leanh::lean_ctor_get(v___x_1218_, 0);
                    v_isSharedCheck_1235_ = (!leanh::lean_is_exclusive(v___x_1218_)) as u8;
                    if v_isSharedCheck_1235_ == 0 {
                        v___x_1230_ = v___x_1218_;
                        v_isShared_1231_ = v_isSharedCheck_1235_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1228_);
                        leanh::lean_dec(v___x_1218_);
                        v___x_1230_ = leanh::lean_box(0);
                        v_isShared_1231_ = v_isSharedCheck_1235_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1223_ =
                    l_Std_Format_pretty(v_a_1219_, v_w_1215_, v_indent_1207_, v_column_1208_);
                leanh::lean_dec(v_w_1215_);
                if v_isShared_1222_ == 0 {
                    leanh::lean_ctor_set(v___x_1221_, 0, v___x_1223_);
                    v___x_1225_ = v___x_1221_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1226_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
                    v___x_1225_ = v_reuseFailAlloc_1226_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1225_;
            }
            4 => {
                if v_isShared_1231_ == 0 {
                    v___x_1233_ = v___x_1230_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1234_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
                    v___x_1233_ = v_reuseFailAlloc_1234_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1233_;
            }
            6 => {
                if v_isShared_1242_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1241_, 0);
                    v___x_1244_ = v___x_1241_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1245_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
                    v___x_1244_ = v_reuseFailAlloc_1245_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra___boxed(
    mut v_s_1247_: *mut leanh::LeanObject,
    mut v_w_1248_: *mut leanh::LeanObject,
    mut v_indent_1249_: *mut leanh::LeanObject,
    mut v_column_1250_: *mut leanh::LeanObject,
    mut v_a_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
    mut v_a_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(
        v_s_1247_,
        v_w_1248_,
        v_indent_1249_,
        v_column_1250_,
        v_a_1251_,
        v_a_1252_,
    );
    leanh::lean_dec(v_a_1252_);
    leanh::lean_dec_ref(v_a_1251_);
    return v_res_1254_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(
    mut v_s_1255_: *mut leanh::LeanObject,
    mut v_w_1256_: *mut leanh::LeanObject,
    mut v_indent_1257_: *mut leanh::LeanObject,
    mut v_column_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v_a_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_suggestion_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_suggestion_1262_ = leanh::lean_ctor_get(v_s_1255_, 0);
    leanh::lean_inc_ref(v_suggestion_1262_);
    leanh::lean_dec_ref(v_s_1255_);
    v___x_1263_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(
        v_suggestion_1262_,
        v_w_1256_,
        v_indent_1257_,
        v_column_1258_,
        v_a_1259_,
        v_a_1260_,
    );
    return v___x_1263_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_Suggestion_pretty___boxed(
    mut v_s_1264_: *mut leanh::LeanObject,
    mut v_w_1265_: *mut leanh::LeanObject,
    mut v_indent_1266_: *mut leanh::LeanObject,
    mut v_column_1267_: *mut leanh::LeanObject,
    mut v_a_1268_: *mut leanh::LeanObject,
    mut v_a_1269_: *mut leanh::LeanObject,
    mut v_a_1270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(
        v_s_1264_,
        v_w_1265_,
        v_indent_1266_,
        v_column_1267_,
        v_a_1268_,
        v_a_1269_,
    );
    leanh::lean_dec(v_a_1269_);
    leanh::lean_dec_ref(v_a_1268_);
    return v_res_1271_;
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(
    mut v_s_1272_: *mut leanh::LeanObject,
    mut v_range_1273_: *mut leanh::LeanObject,
    mut v_a_1274_: *mut leanh::LeanObject,
    mut v_a_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileMap_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut v_a_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileMap_1277_ = leanh::lean_ctor_get(v_a_1274_, 1);
                leanh::lean_inc_ref(v_range_1273_);
                leanh::lean_inc_ref(v_fileMap_1277_);
                v___x_1278_ =
                    l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(v_fileMap_1277_, v_range_1273_);
                v_fst_1279_ = leanh::lean_ctor_get(v___x_1278_, 0);
                leanh::lean_inc(v_fst_1279_);
                v_snd_1280_ = leanh::lean_ctor_get(v___x_1278_, 1);
                leanh::lean_inc(v_snd_1280_);
                leanh::lean_dec_ref(v___x_1278_);
                v___x_1281_ = leanh::lean_box(0);
                v___x_1282_ = l_Lean_Meta_Tactic_TryThis_Suggestion_pretty(
                    v_s_1272_,
                    v___x_1281_,
                    v_fst_1279_,
                    v_snd_1280_,
                    v_a_1274_,
                    v_a_1275_,
                );
                if leanh::lean_obj_tag(v___x_1282_) == 0 {
                    v_a_1283_ = leanh::lean_ctor_get(v___x_1282_, 0);
                    v_isSharedCheck_1292_ = (!leanh::lean_is_exclusive(v___x_1282_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1285_ = v___x_1282_;
                        v_isShared_1286_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1283_);
                        leanh::lean_dec(v___x_1282_);
                        v___x_1285_ = leanh::lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_range_1273_);
                    v_a_1293_ = leanh::lean_ctor_get(v___x_1282_, 0);
                    v_isSharedCheck_1300_ = (!leanh::lean_is_exclusive(v___x_1282_)) as u8;
                    if v_isSharedCheck_1300_ == 0 {
                        v___x_1295_ = v___x_1282_;
                        v_isShared_1296_ = v_isSharedCheck_1300_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1293_);
                        leanh::lean_dec(v___x_1282_);
                        v___x_1295_ = leanh::lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1300_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_fileMap_1277_);
                v___x_1287_ = l_Lean_FileMap_utf8RangeToLspRange(v_fileMap_1277_, v_range_1273_);
                v___x_1288_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1288_, 0, v___x_1287_);
                leanh::lean_ctor_set(v___x_1288_, 1, v_a_1283_);
                leanh::lean_ctor_set(v___x_1288_, 2, v___x_1281_);
                leanh::lean_ctor_set(v___x_1288_, 3, v___x_1281_);
                if v_isShared_1286_ == 0 {
                    leanh::lean_ctor_set(v___x_1285_, 0, v___x_1288_);
                    v___x_1290_ = v___x_1285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
                    v___x_1290_ = v_reuseFailAlloc_1291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1290_;
            }
            3 => {
                if v_isShared_1296_ == 0 {
                    v___x_1298_ = v___x_1295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1299_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
                    v___x_1298_ = v_reuseFailAlloc_1299_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit___boxed(
    mut v_s_1301_: *mut leanh::LeanObject,
    mut v_range_1302_: *mut leanh::LeanObject,
    mut v_a_1303_: *mut leanh::LeanObject,
    mut v_a_1304_: *mut leanh::LeanObject,
    mut v_a_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(
        v_s_1301_,
        v_range_1302_,
        v_a_1303_,
        v_a_1304_,
    );
    leanh::lean_dec(v_a_1304_);
    leanh::lean_dec_ref(v_a_1303_);
    return v_res_1306_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_TryThis(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1 =
        _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1();
    leanh::lean_mark_persistent(
        l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle___aux__1,
    );
    l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle =
        _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle();
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionStyle);
    l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success =
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success();
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success);
    l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis =
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis();
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis);
    l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible =
        _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible();
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible);
    res = l___private_Lean_Meta_TryThis_0__Lean_Meta_Tactic_TryThis_initFn_00___x40_Lean_Meta_TryThis_1556063926____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Tactic_TryThis_format_inputWidth = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_format_inputWidth);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_TryThis(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_TryThis(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Lean_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_TryThis(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_TryThis(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_TryThis(builtin);
}