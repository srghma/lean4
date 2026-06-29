// Lean compiler output
// Module: Std.Http.Data.Headers.Value
// Imports: Init.Data.ToString Std.Http.Internal
use crate::r#gen::Init::Data::List::Basic::{
    l_List_getLast_x3f___redArg, l_List_head_x3f___redArg,
};
use crate::r#gen::Init::Data::Repr::l_String_quote;
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toString, l_String_Slice_trimAscii};
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Prelude::{
    l_Char_utf8Size, l_Function_comp, l_Lean_mkAtom, l_String_hash___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_data, lean_string_utf8_get_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint32_add;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_uint32_dec_le,
};
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value:
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
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value:
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
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_0:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_1:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_2:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5_value:
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
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__6_value:
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
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_0:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_1:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_2:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9_value:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10_value:
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
    m_data: [100, 101, 99, 105, 100, 101, 0],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_0:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_1:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_2:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        14249328086033210933 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__14_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_0:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_1:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_2:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value:
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
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Header_Value_isValidHeaderValue___autoParam:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Header_instBEqValue___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Header_instBEqValue_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_instBEqValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instBEqValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instBEqValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instBEqValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__1_value:
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
    m_data: [118, 97, 108, 117, 101, 0],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__3_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__10_value:
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
        105, 115, 86, 97, 108, 105, 100, 72, 101, 97, 100, 101, 114, 86, 97, 108, 117, 101, 0,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__12_value:
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
    m_data: [95, 0],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__13_value:
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
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__14_value:
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
    m_data: [32, 125, 0],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__17_value:
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
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue_repr___redArg___closed__18_value:
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
        core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instReprValue_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instReprValue___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Header_instReprValue_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Header_instReprValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instReprValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instReprValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instHashableValue___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_Header_instHashableValue___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_instHashableValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instHashableValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instHashableValue___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_String_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_instHashableValue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instHashableValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instHashableValue___closed__2_value: crate::leanh::LeanClosureObject<
    5,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Function_comp as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instHashableValue___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Header_instHashableValue___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Header_instHashableValue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instHashableValue___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instHashableValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instHashableValue___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_instInhabitedValue___closed__0_value: crate::leanh::LeanStringObject<
    1,
> = crate::leanh::LeanStringObject {
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
static mut l_Std_Http_Header_instInhabitedValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instInhabitedValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_instInhabitedValue: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_instInhabitedValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_ofString_x21___closed__0_value: crate::leanh::LeanStringObject<
    28,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 72, 101, 97, 100, 101, 114,
        115, 46, 86, 97, 108, 117, 101, 0,
    ],
};
static mut l_Std_Http_Header_Value_ofString_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_ofString_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_ofString_x21___closed__1_value: crate::leanh::LeanStringObject<
    32,
> = crate::leanh::LeanStringObject {
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
        83, 116, 100, 46, 72, 116, 116, 112, 46, 72, 101, 97, 100, 101, 114, 46, 86, 97, 108, 117,
        101, 46, 111, 102, 83, 116, 114, 105, 110, 103, 33, 0,
    ],
};
static mut l_Std_Http_Header_Value_ofString_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_ofString_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_ofString_x21___closed__2_value: crate::leanh::LeanStringObject<
    23,
> = crate::leanh::LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 104, 101, 97, 100, 101, 114, 32, 118, 97, 108, 117,
        101, 58, 32, 0,
    ],
};
static mut l_Std_Http_Header_Value_ofString_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_ofString_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Header_Value_instToString___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Http_Header_Value_instToString___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Header_Value_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Header_Value_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Header_Value_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_321_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__10;
    v___x_322_ = l_Lean_mkAtom(v___x_321_);
    return v___x_322_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_323_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__12,
    );
    v___x_324_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5;
    v___x_325_ = lean_array_push(v___x_324_, v___x_323_);
    return v___x_325_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_336_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__16;
    v___x_337_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5;
    v___x_338_ = lean_array_push(v___x_337_, v___x_336_);
    return v___x_338_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_339_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__17,
    );
    v___x_340_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__15;
    v___x_341_ = crate::leanh::lean_box(2);
    v___x_342_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_342_, 0, v___x_341_);
    crate::leanh::lean_ctor_set(v___x_342_, 1, v___x_340_);
    crate::leanh::lean_ctor_set(v___x_342_, 2, v___x_339_);
    return v___x_342_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_343_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__18,
    );
    v___x_344_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__13,
    );
    v___x_345_ = lean_array_push(v___x_344_, v___x_343_);
    return v___x_345_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__19,
    );
    v___x_347_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__11;
    v___x_348_ = crate::leanh::lean_box(2);
    v___x_349_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_349_, 0, v___x_348_);
    crate::leanh::lean_ctor_set(v___x_349_, 1, v___x_347_);
    crate::leanh::lean_ctor_set(v___x_349_, 2, v___x_346_);
    return v___x_349_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__20,
    );
    v___x_351_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5;
    v___x_352_ = lean_array_push(v___x_351_, v___x_350_);
    return v___x_352_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__21,
    );
    v___x_354_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__9;
    v___x_355_ = crate::leanh::lean_box(2);
    v___x_356_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_356_, 0, v___x_355_);
    crate::leanh::lean_ctor_set(v___x_356_, 1, v___x_354_);
    crate::leanh::lean_ctor_set(v___x_356_, 2, v___x_353_);
    return v___x_356_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_357_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__22,
    );
    v___x_358_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5;
    v___x_359_ = lean_array_push(v___x_358_, v___x_357_);
    return v___x_359_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_360_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__23,
    );
    v___x_361_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__7;
    v___x_362_ = crate::leanh::lean_box(2);
    v___x_363_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_363_, 0, v___x_362_);
    crate::leanh::lean_ctor_set(v___x_363_, 1, v___x_361_);
    crate::leanh::lean_ctor_set(v___x_363_, 2, v___x_360_);
    return v___x_363_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__24,
    );
    v___x_365_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__5;
    v___x_366_ = lean_array_push(v___x_365_, v___x_364_);
    return v___x_366_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_367_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__25,
    );
    v___x_368_ = l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__4;
    v___x_369_ = crate::leanh::lean_box(2);
    v___x_370_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_370_, 0, v___x_369_);
    crate::leanh::lean_ctor_set(v___x_370_, 1, v___x_368_);
    crate::leanh::lean_ctor_set(v___x_370_, 2, v___x_367_);
    return v___x_370_;
}
pub unsafe fn _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26_once
        ),
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam___closed__26,
    );
    return v___x_371_;
}
pub unsafe fn l_Std_Http_Header_instBEqValue_beq(
    mut v_x_372_: *mut crate::leanh::LeanObject,
    mut v_x_373_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_374_: u8 = 0;
    v___x_374_ = lean_string_dec_eq(v_x_372_, v_x_373_);
    return v___x_374_;
}
pub unsafe fn l_Std_Http_Header_instBEqValue_beq___boxed(
    mut v_x_375_: *mut crate::leanh::LeanObject,
    mut v_x_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_377_: u8 = 0;
    let mut v_r_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_377_ = l_Std_Http_Header_instBEqValue_beq(v_x_375_, v_x_376_);
    crate::leanh::lean_dec_ref(v_x_376_);
    crate::leanh::lean_dec_ref(v_x_375_);
    v_r_378_ = crate::leanh::lean_box((v_res_377_) as usize);
    return v_r_378_;
}
pub unsafe fn l_Std_Http_Header_instDecidableEqValue_decEq(
    mut v_x_381_: *mut crate::leanh::LeanObject,
    mut v_x_382_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_383_: u8 = 0;
    v___x_383_ = lean_string_dec_eq(v_x_381_, v_x_382_);
    return v___x_383_;
}
pub unsafe fn l_Std_Http_Header_instDecidableEqValue_decEq___boxed(
    mut v_x_384_: *mut crate::leanh::LeanObject,
    mut v_x_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_386_: u8 = 0;
    let mut v_r_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Std_Http_Header_instDecidableEqValue_decEq(v_x_384_, v_x_385_);
    crate::leanh::lean_dec_ref(v_x_385_);
    crate::leanh::lean_dec_ref(v_x_384_);
    v_r_387_ = crate::leanh::lean_box((v_res_386_) as usize);
    return v_r_387_;
}
pub unsafe fn l_Std_Http_Header_instDecidableEqValue(
    mut v_x_388_: *mut crate::leanh::LeanObject,
    mut v_x_389_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_390_: u8 = 0;
    v___x_390_ = lean_string_dec_eq(v_x_388_, v_x_389_);
    return v___x_390_;
}
pub unsafe fn l_Std_Http_Header_instDecidableEqValue___boxed(
    mut v_x_391_: *mut crate::leanh::LeanObject,
    mut v_x_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_393_: u8 = 0;
    let mut v_r_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_393_ = l_Std_Http_Header_instDecidableEqValue(v_x_391_, v_x_392_);
    crate::leanh::lean_dec_ref(v_x_392_);
    crate::leanh::lean_dec_ref(v_x_391_);
    v_r_394_ = crate::leanh::lean_box((v_res_393_) as usize);
    return v_r_394_;
}
pub unsafe fn l_Nat_cast___at___00Std_Http_Header_instReprValue_repr_spec__0(
    mut v_a_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_396_ = lean_nat_to_int(v_a_395_);
    return v___x_396_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_410_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_411_ = lean_nat_to_int(v___x_410_);
    return v___x_411_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = l_Std_Http_Header_instReprValue_repr___redArg___closed__0;
    v___x_423_ = lean_string_length(v___x_422_);
    return v___x_423_;
}
pub unsafe fn _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_424_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprValue_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprValue_repr___redArg___closed__15_once),
        _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__15,
    );
    v___x_425_ = lean_nat_to_int(v___x_424_);
    return v___x_425_;
}
pub unsafe fn l_Std_Http_Header_instReprValue_repr___redArg(
    mut v_x_430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: u8 = 0;
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = l_Std_Http_Header_instReprValue_repr___redArg___closed__5;
    v___x_432_ = l_Std_Http_Header_instReprValue_repr___redArg___closed__6;
    v___x_433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprValue_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprValue_repr___redArg___closed__7_once),
        _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__7,
    );
    v___x_434_ = l_String_quote(v_x_430_);
    v___x_435_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_435_, 0, v___x_434_);
    v___x_436_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_436_, 0, v___x_433_);
    crate::leanh::lean_ctor_set(v___x_436_, 1, v___x_435_);
    v___x_437_ = 0;
    v___x_438_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_438_, 0, v___x_436_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_438_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_437_,
    );
    v___x_439_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_439_, 0, v___x_432_);
    crate::leanh::lean_ctor_set(v___x_439_, 1, v___x_438_);
    v___x_440_ = l_Std_Http_Header_instReprValue_repr___redArg___closed__9;
    v___x_441_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_441_, 0, v___x_439_);
    crate::leanh::lean_ctor_set(v___x_441_, 1, v___x_440_);
    v___x_442_ = crate::leanh::lean_box(1);
    v___x_443_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_443_, 0, v___x_441_);
    crate::leanh::lean_ctor_set(v___x_443_, 1, v___x_442_);
    v___x_444_ = l_Std_Http_Header_instReprValue_repr___redArg___closed__11;
    v___x_445_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_445_, 0, v___x_443_);
    crate::leanh::lean_ctor_set(v___x_445_, 1, v___x_444_);
    v___x_446_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_446_, 0, v___x_445_);
    crate::leanh::lean_ctor_set(v___x_446_, 1, v___x_431_);
    v___x_447_ = l_Std_Http_Header_instReprValue_repr___redArg___closed__13;
    v___x_448_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_448_, 0, v___x_446_);
    crate::leanh::lean_ctor_set(v___x_448_, 1, v___x_447_);
    v___x_449_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprValue_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Std_Http_Header_instReprValue_repr___redArg___closed__16_once),
        _init_l_Std_Http_Header_instReprValue_repr___redArg___closed__16,
    );
    v___x_450_ = l_Std_Http_Header_instReprValue_repr___redArg___closed__17;
    v___x_451_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_451_, 0, v___x_450_);
    crate::leanh::lean_ctor_set(v___x_451_, 1, v___x_448_);
    v___x_452_ = l_Std_Http_Header_instReprValue_repr___redArg___closed__18;
    v___x_453_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_453_, 0, v___x_451_);
    crate::leanh::lean_ctor_set(v___x_453_, 1, v___x_452_);
    v___x_454_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_454_, 0, v___x_449_);
    crate::leanh::lean_ctor_set(v___x_454_, 1, v___x_453_);
    v___x_455_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_455_, 0, v___x_454_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_455_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_437_,
    );
    return v___x_455_;
}
pub unsafe fn l_Std_Http_Header_instReprValue_repr(
    mut v_x_456_: *mut crate::leanh::LeanObject,
    mut v_prec_457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_458_ = l_Std_Http_Header_instReprValue_repr___redArg(v_x_456_);
    return v___x_458_;
}
pub unsafe fn l_Std_Http_Header_instReprValue_repr___boxed(
    mut v_x_459_: *mut crate::leanh::LeanObject,
    mut v_prec_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_461_ = l_Std_Http_Header_instReprValue_repr(v_x_459_, v_prec_460_);
    crate::leanh::lean_dec(v_prec_460_);
    return v_res_461_;
}
pub unsafe fn l_Std_Http_Header_instHashableValue___lam__0(
    mut v_self_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_self_464_);
    return v_self_464_;
}
pub unsafe fn l_Std_Http_Header_instHashableValue___lam__0___boxed(
    mut v_self_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_466_ = l_Std_Http_Header_instHashableValue___lam__0(v_self_465_);
    crate::leanh::lean_dec_ref(v_self_465_);
    return v_res_466_;
}
pub unsafe fn l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0(
    mut v_x_475_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_476_: u8 = 0;
    let mut v_head_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: u32 = 0;
    let mut v___x_481_: u32 = 0;
    let mut v___x_482_: u8 = 0;
    let mut v___x_483_: u32 = 0;
    let mut v___x_484_: u32 = 0;
    let mut v___x_485_: u8 = 0;
    let mut v___x_488_: u32 = 0;
    let mut v___x_489_: u32 = 0;
    let mut v___x_490_: u8 = 0;
    let mut v___x_491_: u32 = 0;
    let mut v___x_492_: u32 = 0;
    let mut v___x_493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_475_) == 0 {
                    v___x_476_ = 1;
                    return v___x_476_;
                } else {
                    v_head_477_ = crate::leanh::lean_ctor_get(v_x_475_, 0);
                    v_tail_478_ = crate::leanh::lean_ctor_get(v_x_475_, 1);
                    v___x_488_ = 33;
                    v___x_489_ = crate::leanh::lean_unbox_uint32(v_head_477_);
                    v___x_490_ = lean_uint32_dec_le(v___x_488_, v___x_489_);
                    if v___x_490_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_491_ = 126;
                        v___x_492_ = crate::leanh::lean_unbox_uint32(v_head_477_);
                        v___x_493_ = lean_uint32_dec_le(v___x_492_, v___x_491_);
                        if v___x_493_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_x_475_ = v_tail_478_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_480_ = 32;
                v___x_481_ = crate::leanh::lean_unbox_uint32(v_head_477_);
                v___x_482_ = lean_uint32_dec_eq(v___x_481_, v___x_480_);
                if v___x_482_ == 0 {
                    v___x_483_ = 9;
                    v___x_484_ = crate::leanh::lean_unbox_uint32(v_head_477_);
                    v___x_485_ = lean_uint32_dec_eq(v___x_484_, v___x_483_);
                    if v___x_485_ == 0 {
                        return v___x_485_;
                    } else {
                        v_x_475_ = v_tail_478_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_x_475_ = v_tail_478_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0___boxed(
    mut v_x_495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_496_: u8 = 0;
    let mut v_r_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_496_ = l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0(v_x_495_);
    crate::leanh::lean_dec(v_x_495_);
    v_r_497_ = crate::leanh::lean_box((v_res_496_) as usize);
    return v_r_497_;
}
pub unsafe fn l_Std_Http_Header_Value_ofString_x3f(
    mut v_s_498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_505_: u8 = 0;
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_514_: u32 = 0;
    let mut v___x_515_: u32 = 0;
    let mut v___x_516_: u8 = 0;
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u32 = 0;
    let mut v___x_519_: u32 = 0;
    let mut v___x_520_: u8 = 0;
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_525_: u8 = 0;
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: u8 = 0;
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: u32 = 0;
    let mut v___x_532_: u32 = 0;
    let mut v___x_533_: u8 = 0;
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u32 = 0;
    let mut v___x_536_: u32 = 0;
    let mut v___x_537_: u8 = 0;
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_499_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_500_ = lean_string_utf8_byte_size(v_s_498_);
                v___x_501_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_501_, 0, v_s_498_);
                crate::leanh::lean_ctor_set(v___x_501_, 1, v___x_499_);
                crate::leanh::lean_ctor_set(v___x_501_, 2, v___x_500_);
                v___x_502_ = l_String_Slice_trimAscii(v___x_501_);
                v_val_503_ = l_String_Slice_toString(v___x_502_);
                crate::leanh::lean_dec_ref(v___x_502_);
                crate::leanh::lean_inc_ref(v_val_503_);
                v___x_526_ = lean_string_data(v_val_503_);
                v___x_527_ =
                    l_List_all___at___00Std_Http_Header_Value_ofString_x3f_spec__0(v___x_526_);
                if v___x_527_ == 0 {
                    crate::leanh::lean_dec(v___x_526_);
                    crate::leanh::lean_dec_ref(v_val_503_);
                    v___x_528_ = crate::leanh::lean_box(0);
                    return v___x_528_;
                } else {
                    v___x_529_ = l_List_head_x3f___redArg(v___x_526_);
                    crate::leanh::lean_dec(v___x_526_);
                    if crate::leanh::lean_obj_tag(v___x_529_) == 0 {
                        v___y_505_ = v___x_527_;
                        state = 1;
                        continue;
                    } else {
                        v_val_530_ = crate::leanh::lean_ctor_get(v___x_529_, 0);
                        crate::leanh::lean_inc(v_val_530_);
                        crate::leanh::lean_dec_ref_known(v___x_529_, 1);
                        v___x_531_ = 33;
                        v___x_532_ = crate::leanh::lean_unbox_uint32(v_val_530_);
                        v___x_533_ = lean_uint32_dec_le(v___x_531_, v___x_532_);
                        if v___x_533_ == 0 {
                            crate::leanh::lean_dec(v_val_530_);
                            crate::leanh::lean_dec_ref(v_val_503_);
                            v___x_534_ = crate::leanh::lean_box(0);
                            return v___x_534_;
                        } else {
                            v___x_535_ = 126;
                            v___x_536_ = crate::leanh::lean_unbox_uint32(v_val_530_);
                            crate::leanh::lean_dec(v_val_530_);
                            v___x_537_ = lean_uint32_dec_le(v___x_536_, v___x_535_);
                            if v___x_537_ == 0 {
                                crate::leanh::lean_dec_ref(v_val_503_);
                                v___x_538_ = crate::leanh::lean_box(0);
                                return v___x_538_;
                            } else {
                                v___y_505_ = v___x_527_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v___y_505_ == 0 {
                    crate::leanh::lean_dec_ref(v_val_503_);
                    v___x_506_ = crate::leanh::lean_box(0);
                    return v___x_506_;
                } else {
                    crate::leanh::lean_inc_ref(v_val_503_);
                    v___x_507_ = lean_string_data(v_val_503_);
                    v___x_508_ = l_List_getLast_x3f___redArg(v___x_507_);
                    crate::leanh::lean_dec(v___x_507_);
                    if crate::leanh::lean_obj_tag(v___x_508_) == 0 {
                        v___x_509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_509_, 0, v_val_503_);
                        return v___x_509_;
                    } else {
                        v_val_510_ = crate::leanh::lean_ctor_get(v___x_508_, 0);
                        v_isSharedCheck_525_ = (!crate::leanh::lean_is_exclusive(v___x_508_)) as u8;
                        if v_isSharedCheck_525_ == 0 {
                            v___x_512_ = v___x_508_;
                            v_isShared_513_ = v_isSharedCheck_525_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_510_);
                            crate::leanh::lean_dec(v___x_508_);
                            v___x_512_ = crate::leanh::lean_box(0);
                            v_isShared_513_ = v_isSharedCheck_525_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_514_ = 33;
                v___x_515_ = crate::leanh::lean_unbox_uint32(v_val_510_);
                v___x_516_ = lean_uint32_dec_le(v___x_514_, v___x_515_);
                if v___x_516_ == 0 {
                    crate::leanh::lean_del_object(v___x_512_);
                    crate::leanh::lean_dec(v_val_510_);
                    crate::leanh::lean_dec_ref(v_val_503_);
                    v___x_517_ = crate::leanh::lean_box(0);
                    return v___x_517_;
                } else {
                    v___x_518_ = 126;
                    v___x_519_ = crate::leanh::lean_unbox_uint32(v_val_510_);
                    crate::leanh::lean_dec(v_val_510_);
                    v___x_520_ = lean_uint32_dec_le(v___x_519_, v___x_518_);
                    if v___x_520_ == 0 {
                        crate::leanh::lean_del_object(v___x_512_);
                        crate::leanh::lean_dec_ref(v_val_503_);
                        v___x_521_ = crate::leanh::lean_box(0);
                        return v___x_521_;
                    } else {
                        if v_isShared_513_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_512_, 0, v_val_503_);
                            v___x_523_ = v___x_512_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_524_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_524_, 0, v_val_503_);
                            v___x_523_ = v_reuseFailAlloc_524_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_Http_Header_Value_ofString_x21_spec__0(
    mut v_msg_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_540_ = l_Std_Http_Header_instInhabitedValue___closed__0;
    v___x_541_ = lean_panic_fn_borrowed(v___x_540_, v_msg_539_);
    return v___x_541_;
}
pub unsafe fn l_Std_Http_Header_Value_ofString_x21(
    mut v_s_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_s_545_);
    v___x_546_ = l_Std_Http_Header_Value_ofString_x3f(v_s_545_);
    if crate::leanh::lean_obj_tag(v___x_546_) == 0 {
        let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_547_ = l_Std_Http_Header_Value_ofString_x21___closed__0;
        v___x_548_ = l_Std_Http_Header_Value_ofString_x21___closed__1;
        v___x_549_ = crate::leanh::lean_unsigned_to_nat(91);
        v___x_550_ = crate::leanh::lean_unsigned_to_nat(12);
        v___x_551_ = l_Std_Http_Header_Value_ofString_x21___closed__2;
        v___x_552_ = l_String_quote(v_s_545_);
        v___x_553_ = lean_string_append(v___x_551_, v___x_552_);
        crate::leanh::lean_dec_ref(v___x_552_);
        v___x_554_ =
            l_mkPanicMessageWithDecl(v___x_547_, v___x_548_, v___x_549_, v___x_550_, v___x_553_);
        crate::leanh::lean_dec_ref(v___x_553_);
        v___x_555_ = l_panic___at___00Std_Http_Header_Value_ofString_x21_spec__0(v___x_554_);
        return v___x_555_;
    } else {
        let mut v_val_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_545_);
        v_val_556_ = crate::leanh::lean_ctor_get(v___x_546_, 0);
        crate::leanh::lean_inc(v_val_556_);
        crate::leanh::lean_dec_ref_known(v___x_546_, 1);
        return v_val_556_;
    }
}
pub unsafe fn l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(
    mut v_s_557_: *mut crate::leanh::LeanObject,
    mut v_p_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_560_: u32 = 0;
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: u8 = 0;
    let mut v___x_567_: u32 = 0;
    let mut v___x_568_: u32 = 0;
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: u32 = 0;
    let mut v___x_571_: u8 = 0;
    let mut v___x_572_: u32 = 0;
    let mut v___x_573_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_565_ = lean_string_utf8_byte_size(v_s_557_);
                v___x_566_ = lean_nat_dec_eq(v_p_558_, v___x_565_);
                if v___x_566_ == 0 {
                    v___x_567_ = lean_string_utf8_get_fast(v_s_557_, v_p_558_);
                    v___x_568_ = 65;
                    v___x_569_ = lean_uint32_dec_le(v___x_568_, v___x_567_);
                    if v___x_569_ == 0 {
                        v___y_560_ = v___x_567_;
                        state = 1;
                        continue;
                    } else {
                        v___x_570_ = 90;
                        v___x_571_ = lean_uint32_dec_le(v___x_567_, v___x_570_);
                        if v___x_571_ == 0 {
                            v___y_560_ = v___x_567_;
                            state = 1;
                            continue;
                        } else {
                            v___x_572_ = 32;
                            v___x_573_ = lean_uint32_add(v___x_567_, v___x_572_);
                            v___y_560_ = v___x_573_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_p_558_);
                    return v_s_557_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_p_558_);
                v___x_561_ = lean_string_utf8_set(v_s_557_, v_p_558_, v___y_560_);
                v___x_562_ = l_Char_utf8Size(v___y_560_);
                v___x_563_ = lean_nat_add(v_p_558_, v___x_562_);
                crate::leanh::lean_dec(v___x_562_);
                crate::leanh::lean_dec(v_p_558_);
                v_s_557_ = v___x_561_;
                v_p_558_ = v___x_563_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Header_Value_is(
    mut v_s_574_: *mut crate::leanh::LeanObject,
    mut v_h_575_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    v___x_576_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_577_ = l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(v_s_574_, v___x_576_);
    v___x_578_ = l_String_mapAux___at___00Std_Http_Header_Value_is_spec__0(v_h_575_, v___x_576_);
    v___x_579_ = lean_string_dec_eq(v___x_577_, v___x_578_);
    crate::leanh::lean_dec_ref(v___x_578_);
    crate::leanh::lean_dec_ref(v___x_577_);
    return v___x_579_;
}
pub unsafe fn l_Std_Http_Header_Value_is___boxed(
    mut v_s_580_: *mut crate::leanh::LeanObject,
    mut v_h_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_582_: u8 = 0;
    let mut v_r_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_582_ = l_Std_Http_Header_Value_is(v_s_580_, v_h_581_);
    v_r_583_ = crate::leanh::lean_box((v_res_582_) as usize);
    return v_r_583_;
}
pub unsafe fn l_Std_Http_Header_Value_instToString___lam__0(
    mut v_v_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_v_584_);
    return v_v_584_;
}
pub unsafe fn l_Std_Http_Header_Value_instToString___lam__0___boxed(
    mut v_v_585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_586_ = l_Std_Http_Header_Value_instToString___lam__0(v_v_585_);
    crate::leanh::lean_dec_ref(v_v_585_);
    return v_res_586_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Headers_Value(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Headers_Value(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Http_Header_Value_isValidHeaderValue___autoParam =
        _init_l_Std_Http_Header_Value_isValidHeaderValue___autoParam();
    crate::leanh::lean_mark_persistent(l_Std_Http_Header_Value_isValidHeaderValue___autoParam);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Headers_Value(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Internal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Headers_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Headers_Value(builtin);
}
